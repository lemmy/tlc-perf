#!/bin/bash

## Debugging
set -x

## ID of this script
PID=$$

## command line parameters (seq of workers)
WORKER_SEQ=$1

## grid job identifier
JOB_ID=$OAR_JOB_ID

## list of hosts (host appears multiple times for each core)
FILE_NODES=`cat $OAR_FILE_NODES | uniq | sort`

## which models to check
MODEL_NAMES="l10_n6 l12_n6"

## root dir
ROOT_DIR=/home/mkuppe/grid5000.git

## where the model _files_ are kept
SPEC_PATH=$ROOT_DIR/models/

## tools not available in the grid
JAVA_PATH=$ROOT_DIR/tools/jre/bin/java
PSSH_PATH=$ROOT_DIR/tools/pssh/bin/pssh

## local tools in the grid
UNZIP_PATH=/usr/bin/unzip
GIT_PATH=/usr/bin/git

## staging area to reduce load on NFS
TARGET_DIR=/tmp/$PID
TARGET_TLA_DIR=$TARGET_DIR/tla
TARGET_SPEC_DIR=$TARGET_DIR/spec

## 
RESULT_DIR=$ROOT_DIR/results/$MODEL_NAME-$JOB_ID-w$WORKER_COUNT

## go to root
cd $ROOT_DIR

## cleanup old leftovers
rm -rf $TARGET_SPEC_DIR
rm -rf $TARGET_TLA_DIR

## extract tla.zip distribution to (local) target directory
$UNZIP_PATH -q $ROOT_DIR/tla.zip -d $TARGET_DIR/

## copy spec to target directory
cp -a $SPEC_PATH $TARGET_SPEC_DIR

## select server (first host in the list)
SERVER_NAME=`head -1 $FILE_NODES`


## loop over models
for MODEL_NAME in $MODEL_NAMES;
do
    ## loop over workers
    for WORKER_COUNT in {$WORKER_SEQ};
    do
	##
	## write job information
        
        ## create result directory
	mkdir -p $RESULT_DIR
	
	##
	## spawn workers in the bg with pssh (they wait for the server)
	
	## create a worker file for pssh
	WORKER_FILE=$TARGET_DIR/$JOB_ID-w$WORKER_COUNT-m$MODEL_NAME.txt
	tail -$WORKER_COUNT $FILE_NODES > $WORKER_FILE
	
	## spawn pssh process
	$PSSH_PATH -t -1 -p $WORKER_COUNT -h $WORKER_FILE '$mkdir -p $RESULT_DIR/`hostname -f`-$$ && $JAVA_PATH -Xmx2096m -cp $TARGET_TLA_DIR tlc2.tool.distributed.TLCWorker $SERVER_NAME > $RESULT_DIR/`hostname -f`-$$/worker.out 2>&12' &

	##
	## spawn server in fg
        
        ## log amount of workers to result directory
	echo $WORKER_COUNT > $RESULT_DIR/worker_count.txt

        ## log start timestamp to result directory
	echo `date -u +%T` > $RESULT_DIR/start_time.txt

        ## spawn Java VM with server
        $JAVA_PATH -Xmx2096m -cp $TARGET_TLA_DIR:$TARGET_TLA_DIR/lib/aspectjrt.jar -javaagent:$TARGET_TLA_DIR/lib/aspectjweaver.jar -Dorg.aspectj.weaver.showWeaveInfo=true -Daj.weaving.verbose=true -Dtlc2.tool.distributed.TLCStatistics.path=$RESULT_DIR/ -Djava.rmi.server.logCalls=true -Dtlc2.tool.distributed.TLCServer.expectedWorkerCount=$WORKER_COUNT tlc2.tool.distributed.TLCServer $TARGET_SPEC_DIR/MC.tla > $RESULT_DIR/server.out 2> $RESULT_DIR/server.err

        ## log start timestamp to result directory
	echo `date -u +%T` > $RESULT_DIR/end_time.txt
	
	##
	## persistently store result (implicitly like a sleep letting workers/server shutdown)
	$GIT_PATH pull origin master
	$GIT_PATH add -u $RESULT_DIR/*
	$GIT_PATH commit -m '$'
	$GIT_PATH push origin master
    done
done



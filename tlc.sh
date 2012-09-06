#!/bin/bash

# Parameters
# 1: Start (Num of workers)
# 2: End   (Num of workers)
# 3: Stepping (Increment of workers)
# optional
# 4: Model names
# 5: JOB_ID (Identifier for current run)
# 6: OAR_FILE_Nodes (ascii file with list of all nodes (one node per line))
# 7: ROOT_DIR (location of git repo)
# 8: TARGET_PREFIX (location of tmp files)
# 9: MUNIN_DIR (location of munin generated rrds)
# 10: WORKER_VM_PROPS (extra -X JVM properties worker side)
# 11: WORKER_SYS_PROPS (extra -D JVM properties worker side)
# 12: MASTER_VM_PROPS (extra -X JVM properties master side)
# 13: MASTER_SYS_PROPS (extra -D JVM properties master side)
# 14: WORKER_CLASS (Java main class used by worker nodes)
# 15: MASTER_CLASS (Java main class used by master node)

## ID of this script
PID=$$

START=$1
END=$2
STEP=$3

TIMESTAMP=`date -u +%T`

## grid job identifier
JOB_ID=${5-$OAR_JOB_ID}

## which models to check
MODEL_NAMES=${4-"l12_n6 l14_n6"}

## root dir
ROOT_DIR=${7-/home/mkuppe/grid5000.git}

## where the model _files_ are kept
SPEC_PATH=$ROOT_DIR/models/

## tools not available in the grid
JAVA_PATH=$ROOT_DIR/tools/jre/bin/java
PSSH_PATH=$ROOT_DIR/tools/pssh/bin/pssh
CONVERTRRD_PATH=$ROOT_DIR/tools/convertRRD.sh

## local tools in the grid
UNZIP_PATH=/usr/bin/unzip
GIT_PATH=/usr/bin/git

# Params
WORKER_VM_PROPS=${10-"-Xmx2096m -Xms2096m"}
WORKER_SYS_PROPS=${11-""}
WORKER_CLASS=${14-"tlc2.tool.distributed.fp.TLCWorkerAndFPSet"}
MASTER_VM_PROPS=${12-"-Xmx2096m -Xms2096m"}
MASTER_SYS_PROPS=${13-""}
MASTER_CLASS=${15-"tlc2.tool.distributed.TLCServer"}

## staging area to reduce load on NFS
TARGET_PREFIX=${8-"/tmp"}
TARGET_DIR=$TARGET_PREFIX/$PID
TARGET_TLA_DIR=$TARGET_DIR/tla
TARGET_SPEC_DIR=$TARGET_DIR/spec

## go to root
cd $ROOT_DIR

## cleanup old leftovers
rm -rf $TARGET_SPEC_DIR
rm -rf $TARGET_TLA_DIR

## extract tla.zip distribution to (local) target directory for server
$UNZIP_PATH -qq $ROOT_DIR/dist/tla.zip -d $TARGET_DIR/

## copy spec to target directory
cp -a $SPEC_PATH $TARGET_SPEC_DIR

## select server (first host in the list)
SERVER_NAME=`hostname -f`

## list of hosts (host appears multiple times for each core)
FILE_NODES=$TARGET_DIR/$JOB_ID-hosts.txt
cat ${6-$OAR_FILE_NODES} |grep -v $HOSTNAME | uniq | sort > $FILE_NODES

## loop over models
for MODEL_NAME in $MODEL_NAMES;
do
    echo "checking model: $MODEL_NAME"

    ## loop over workers
    for ((WORKER_COUNT=$START ; $WORKER_COUNT $END; WORKER_COUNT = $WORKER_COUNT $STEP));
    do
	echo "with workers: $WORKER_COUNT"

	##
	WORKER_COUNT_PADDED=$(printf %03d $WORKER_COUNT)
	RESULT_DIR=$ROOT_DIR/results/$MODEL_NAME-w$WORKER_COUNT_PADDED-$JOB_ID-$TIMESTAMP
	
	##
	## write job information
        
        ## create result directory
	mkdir -p $RESULT_DIR

	## Write TLC build and rev
	$UNZIP_PATH $ROOT_DIR/dist/tla2tools.jar META-INF/MANIFEST.MF -d /tmp
	mv /tmp/META-INF/MANIFEST.MF $RESULT_DIR/
	
	##
	## spawn workers in the bg with pssh (they wait for the server)
	
	## create a worker file for pssh
	WORKER_FILE=$TARGET_DIR/$JOB_ID-w$WORKER_COUNT-m$MODEL_NAME.txt
	tail -$WORKER_COUNT $FILE_NODES > $WORKER_FILE
	
	## spawn pssh process
	if [ $WORKER_COUNT -gt 0 ]; then
	    if [ $WORKER_CLASS = "osgi" ]; then
		$PSSH_PATH -O UserKnownHostsFile=/dev/null -O StrictHostKeyChecking=no -t -1 -p $WORKER_COUNT -h $WORKER_FILE $JAVA_PATH $WORKER_VM_PROPS -Dorg.lamport.tla.distributed.consumer.TLCWorkerConsumer.uri=rmi://$SERVER_NAME:10997 -Dorg.lamport.tla.distributed.consumer.DistributedFPSetConsumer.uri=rmi://$SERVER_NAME:10997 -jar $ROOT_DIR/dist/disttlc/org.eclipse.osgi_3.7.0.v20110613.jar $WORKER_SYS_PROPS & PSSH_PID=$!
	    else
		$PSSH_PATH -O UserKnownHostsFile=/dev/null -O StrictHostKeyChecking=no -t -1 -p $WORKER_COUNT -h $WORKER_FILE $JAVA_PATH $WORKER_VM_PROPS -cp $ROOT_DIR/dist/tla2tools.jar $WORKER_SYS_PROPS $WORKER_CLASS $SERVER_NAME & PSSH_PID=$!
	    fi
	fi

	##
	## spawn server in fg
        
        ## log amount of workers to result directory
	echo $WORKER_COUNT > $RESULT_DIR/worker_count.txt
	cat $WORKER_FILE > $RESULT_DIR/workers.txt
	
	echo `hostname -f` > $RESULT_DIR/server.txt

        ## log start timestamp to result directory
	echo `date -u +%T` > $RESULT_DIR/start_time.txt

        ## spawn Java VM with server
	export CLASSPATH=$TARGET_TLA_DIR:$TARGET_TLA_DIR/lib/*:$CLASSPATH
	
	## if agent jar file is present, we want it as the javaagent parameter
	if [ -e $TARGET_TLA_DIR/lib/aspectjweaver.jar ]; then
	    AGENT_OPTS="-javaagent:$TARGET_TLA_DIR/lib/aspectjweaver.jar"
	else
	    AGENT_OPTS=""
	fi

	## Activate remote debugging interface to make it possible to connect to the VM during the run
	MASTER_VM_PROPS=$MASTER_VM_PROPS" -Xdebug -Xrunjdwp:transport=dt_socket,server=y,suspend=n,address=1044"

	if [ $MASTER_CLASS = "tlc2.TLC" ]; then
	    cd $TARGET_SPEC_DIR
	    $JAVA_PATH $MASTER_VM_PROPS $AGENT_OPTS $MASTER_SYS_PROPS -Dtlc2.tool.distributed.TLCStatistics.path=$RESULT_DIR/ $MASTER_CLASS $TLC_PARAMS $MODEL_NAME 2>&1 | tee $RESULT_DIR/server.out
	    # cd back to previous directory
	    cd -
	else
	    if [ $WORKER_CLASS = "tlc2.tool.distributed.fp.TLCWorkerAndFPSet" ]; then
		$JAVA_PATH $MASTER_VM_PROPS $AGENT_OPTS $MASTER_SYS_PROPS -Dtlc2.tool.distributed.TLCServer.expectedFPSetCount=$WORKER_COUNT -Dtlc2.tool.distributed.TLCServer.expectedWorkerCount=$WORKER_COUNT -Dtlc2.tool.distributed.TLCStatistics.path=$RESULT_DIR/ $MASTER_CLASS $TLC_PARAMS $TARGET_SPEC_DIR/$MODEL_NAME.tla 2>&1 | tee $RESULT_DIR/server.out
	    else
		$JAVA_PATH $MASTER_VM_PROPS $AGENT_OPTS $MASTER_SYS_PROPS -Dtlc2.tool.distributed.TLCServer.expectedWorkerCount=$WORKER_COUNT -Dtlc2.tool.distributed.TLCStatistics.path=$RESULT_DIR/ $MASTER_CLASS $TLC_PARAMS $TARGET_SPEC_DIR/$MODEL_NAME.tla 2>&1 | tee $RESULT_DIR/server.out
	    fi
	fi

	## Explicitly kill any stuck (remote) workers by killing the PSSH process that forked them. If workers exited normally, calling kill has no effect.
	## (This code ignores the fact that the PSSH process could exit normally and a new process get the same pid assigned in the meantime)
	kill $PSSH_PID > /dev/null 2>&1

        ## log start timestamp to result directory
	echo `date -u +%T` > $RESULT_DIR/end_time.txt

	# locally
	$CONVERTRRD_PATH $RESULT_DIR $9 > /dev/null

	##
	## persistently store result (implicitly like a sleep letting workers/server shutdown)
	#$GIT_PATH pull origin master
	$GIT_PATH add $RESULT_DIR/* > /dev/null
	find $RESULT_DIR -type d | xargs -I {} $GIT_PATH add {}/* > /dev/null
	$GIT_PATH commit -m ''$RESULT_DIR'' > /dev/null
	#$GIT_PATH push origin master
    done
done



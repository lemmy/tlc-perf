#!/bin/bash

#set -x

RRDTOOL_PATH=`which rrdtool`
OUTPUT_DIR=$1

for i in `find . -iname *.xml`
do
    # Ignore heading
    #LINE=`cat $i | tail -1`

    # cut of L and N which is no recorded elsewhere
    MODEL_NAME=`echo $i | cut -d '/' -f 2`
    L=`echo $MODEL_NAME | cut -d '_' -f 1`
    N=`echo $MODEL_NAME | cut -d '_' -f 2 | cut -d '-' -f 1`
    WORKER=`echo $MODEL_NAME | cut -d '-' -f 2`
    HOST=`echo $i | cut -d '/' -f 3`
    RRD=`echo $i | cut -d '/' -f 4 | sed 's/xml/rrd/g'`

    # OAR job id
    JOB_ID=`echo $MODEL_NAME | cut -d '-' -f 3`

    # write name of cluster (default to bordeaux/bordereau)
    SERVERTXT=`dirname $i`/../server.txt
    if [ -e $SERVERTXT ]; then
	CLUSTER=`cat $SERVERTXT | cut -d '.' -f 1 | cut -d '-' -f 1`
        SITE=`cat $SERVERTXT | cut -d '.' -f 2`
    else
	CLUSTER="bordeaux"
        SITE="bordereau"
    fi

    EXPERIMENT=$SITE-$JOB_ID-$WORKER-$L-$N

    # create subfolder if needed
    TARGET_DIR=$OUTPUT_DIR/$EXPERIMENT/$HOST
    test -e $TARGET_DIR || mkdir -p $TARGET_DIR

    # Restore rrd into output dir
    if [ -e $TARGET_DIR/$RRD ]; then
	echo "Skipping $i, already present"
    else
        echo "Restoring $i to $TARGET_DIR"
	$RRDTOOL_PATH restore $i $TARGET_DIR/$RRD
    fi
done


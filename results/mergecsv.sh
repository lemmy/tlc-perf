#!/bin/bash

# Loop over all .csv files
COUNT=0;
for i in `find . -iname server.csv`
do
    # Ignore heading
    LINE=`cat $i | tail -1`

    # cut of L and N which is no recorded elsewhere
    MODEL_NAME=`echo $i | cut -d '/' -f 2`
    L=`echo $MODEL_NAME | cut -d '_' -f 1`
    N=`echo $MODEL_NAME | cut -d '_' -f 2 | cut -d '-' -f 1`

    # OAR job id
    JOB_ID=`echo $MODEL_NAME | cut -d '-' -f 3`

    # write name of cluster (default to bordeaux/bordereau)
    SERVERTXT=`dirname $i`/server.txt
    if [ -e $SERVERTXT ]; then
	CLUSTER=`cat $SERVERTXT | cut -d '.' -f 1 | cut -d '-' -f 1`
        SITE=`cat $SERVERTXT | cut -d '.' -f 2`
    else
	CLUSTER="bordeaux"
        SITE="bordereau"
    fi
    
    # Only print column headings once
    if [ $COUNT -eq 0 ]; then
	let COUNT++
        HEADING=`cat $i | head -1`
        echo "L,N,Site,Cluster,OARJobID,$HEADING"
    fi

    # print everything else
    echo ${L:1},${N:1},$SITE,$CLUSTER,$JOB_ID,$LINE
done


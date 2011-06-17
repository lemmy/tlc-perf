#!/bin/bash

# Loop over all .csv files
COUNT=0;
for i in `find . -iname server.csv`
do
    COUNT=`echo $COUNT + 1 | bc`

    # Ignore heading
    LINE=`cat $i | tail -1`

    # cut of L and N which is no recorded elsewhere
    MODEL_NAME=`echo $i | cut -d '/' -f 2`
    L=`echo $MODEL_NAME | cut -d '_' -f 1`
    N=`echo $MODEL_NAME | cut -d '_' -f 2 | cut -d '-' -f 1`

    # OAR job id
    JOB_ID=`echo $MODEL_NAME | cut -d '-' -f 3`

    # fix elapsed time for excel/calc (convert to elapsed seconds)
    ELAPSED=`date -d "$(echo $LINE | cut -d ',' -f 9)" +%s`

    # Only print column headings once
    if [ $COUNT -eq 1 ]; then
        HEADING=`cat $i | head -1`
        echo "L,N,ElapsedTime,OARJobID,$HEADING"
    fi

    # print everything else
    echo ${L:1},${N:1},$ELAPSED,$JOB_ID,$LINE
done


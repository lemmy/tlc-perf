#!/bin/bash

#set -x

RRDTOOL_PATH=`which rrdtool`

TMP_DIR=/tmp/$$
RESULT_DIR=$1
RRD_DIR=${2-"/var/lib/munin/tlc"}
OUT_DIR=$RESULT_DIR/`hostname -s`

mkdir -p $TMP_DIR
mkdir -p $OUT_DIR

# locally
for RRD in `find $RRD_DIR/*.rrd`;
do
    XMLFILE=`echo ${RRD%%.rrd} | sed "s#$RRD_DIR/##g"`
    $RRDTOOL_PATH dump $RRD | xmlstarlet ed -d '//comment()' > $TMP_DIR/$XMLFILE.xml
done

tar cvfj $RESULT_DIR/munin.tar.bz2 $TMP_DIR



#!/bin/bash

set -x

RRDTOOL_PATH=`which rrdtool`
RESULT_DIR=$1

OUT_DIR=$RESULT_DIR/`hostname -s`

mkdir -p $OUT_DIR

# explicitly flush rrd data to disk by regenerating munin graphs locally
sudo -u munin /usr/bin/munin-cron

# locally
for RRD in `find /var/lib/munin/tlc/*.rrd`;
do
    XMLFILE=`echo $RRD | sed 's#/var/lib/munin/tlc/tlc-##g' | cut -f 1 -d '.'`
    $RRDTOOL_PATH dump $RRD $OUT_DIR/$XMLFILE.xml
done



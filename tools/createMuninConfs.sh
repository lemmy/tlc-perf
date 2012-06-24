#!/bin/bash

NODES=$1

for node in `cat $1`
do
    touch /tmp/$node.conf
    echo "[$node] address $node" > /tmp/$node.conf
    sudo mv /tmp/$node.conf /etc/munin/munin-conf.d/
done
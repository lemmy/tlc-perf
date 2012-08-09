#!/bin/bash
set -x
kadeploy3 -e squeeze-x64-nfs -o /home/mkuppe/$OAR_JOB_ID.nodes -f $OAR_FILE_NODES -k
taktuk -l root -s -o connector -o status -o output='"$host: $line\n"' -f /home/mkuppe/$OAR_JOB_ID.nodes broadcast exec [ "/home/mkuppe/grid5000.git/cloud/G5k/Provision.sh" ]
ssh `head -n 1 /home/mkuppe/$OAR_JOB_ID.nodes` "/home/mkuppe/grid5000.git/tlc.sh $1 $2 $3 $4 $5$OAR_JOB_ID /home/mkuppe/$OAR_JOB_ID.nodes /home/mkuppe/grid5000.git /tmp /var/lib/munin/tlc '$6' '$7' '$8' '$9' '$10' '$11'"


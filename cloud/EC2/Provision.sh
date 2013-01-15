#!/bin/bash
#
# To run this script, the ec2-ami-tools have to be installed on your system. 
# Afterwards the following command will create a new instance and execute this script right after system startup. 
# The system will be set up for TLC development afterwards.
#
# ec2-run-instances -m --key markus@kuppe.org --instance-type m2.4xlarge --user-data-file /path/to/Provision.sh ami-c162a9a8
#

# Exit if this script has run before (e.g. booting up a custom EC2 AMI)
# The decision is simply based on the existence of the kuppe user account
id kuppe && exit 0

# format and mount second ephemeral disk
/sbin/mkfs.ext4 /dev/xvbc
mkdir /mnt2
mount /dev/xvdc /mnt2
chmod 777 /mnt2

# switch to mount to use the instance ephemeral storage rather than ESB
cd /mnt

# create user kuppe and setup public key
useradd --home /mnt/kuppe -m kuppe -s /bin/bash -G admin,sudo
ln -s /mnt/kuppe /home/kuppe
mkdir /home/kuppe/.ssh
# personal one to ssh into the box
echo "ssh-rsa AAAAB3NzaC1yc2EAAAADAQABAAABAQDY+EiWONhPeuupD26mtePrFDzel5ewHcLow0FfdCNnTyRdXRJVo8iyDROP5YyNfphmgezsRcv62sXAft4sqKoVw14luX9XPjNWDARsTbPOyhBTsJe6qMm/8nZ78zGbL8EEWVE52l3rx2MWYy67VwBaAP5szVVpmj+7VJ4fCh/1Vp9ORgOxwgzdpkt2qx8Tn5qVkjOwxqpGsANsaXLmfdRo9eXFXO845Ok7bytPqdwJsSoB2tRUH8rwHrVPQsJsXYnTQFKf8mhf21uxhdsnHg4jWEk1My/XI+x/mjR8ksQWcpjumVAFw7flMD1ZYBijo3CR+b2GtV4uKTxjf8bbEcBn kuppe@ec2.amazonaws.com" >> /home/kuppe/.ssh/authorized_keys
echo "ssh-rsa AAAAB3NzaC1yc2EAAAADAQABAAABAQDaFesWicuMjw2s9+4rl36IP781nZ07Vasir5nybvVmmN2wDV1sTcv0iS8VgH54qxmCtV2zQiub0gMq4kHnnTVMKdlMGOyhbvC4X3UVmhJFrD+8UG5bmsbEVXjmgh7Y1oEoldrIf4DlnnHcetdSwuMvV5xqI3iZ+8xg0j9pnN8a9xWj5dUv/rkq2Z5So7AYd+aVCU6uETh8N9fsMZSo/Eu9A+vYvwWhsysY0S8m7wr9zkd71fjc1mTPlAsZGtzACRswrk3S2NLdCd7NNOU1jT5QVffc7poTeCngMFrXjmtUPZZQxOfA6oDq0rSCep+TgjVa2KQAypMDQTjKfkwjaklL markus@kuppe.org" >> /home/kuppe/.ssh/authorized_keys
echo "ssh-rsa AAAAB3NzaC1yc2EAAAABIwAAAQEAy4sKgMk2QS8wKze690bmar4cJXz2/AGJr36uJ8gds6zAhM9cyQ4GEuOgOORAOWcUAg3HZI65GdCqtHE+P4t9P5Qi1bE+d24ZL0Ebg6z5P8f8XvSId7Gd/p7YXgCcOJj4nxRHRr3fmHvLw+s0PLCaCg5uqShOBhyxbD8H8pgh4WqxUhHtAeIV+OhuazgLjCYL9b2DFSUtad6j+c+podcZGOJq+DLhP3NWJI5eiO2u7PuX06sRCTo4UxZlP+bvjhU7tH/VRIg9R7CO9TvmMykJEAwa6G5vf4kCFeh9f0pYA26UUFg8z0P2ki7+Z0zHXD3w7zbDYzZ9snFY9RtajtNkXw== markus@kuppe.org" >> /home/kuppe/.ssh/authorized_keys
echo "ssh-rsa AAAAB3NzaC1yc2EAAAADAQABAAABAQDZWGzBB+uHHtLOw0PsizjW4YpHs4u+8Wo4Exy+Yr+iYcVCNzAcR8e+ixpve14FaVN9ia7Trjd8xC8j/AWiQ+oMHXdJZQNrfKUtUxebSxA0yqlE3WXSjq+uAyRUT8czc5aM8h93iVz5AZwbUPy6ayxFr0PrVE/XmA+ZSAZ2pbPOg/KVZhqMILznCwhQ5lyUsIMSdZNIUlZH5+347zEvhJFhoPy95c4qs5qWvEaXD9Dxu/wCHqIv0KAKC4dxr+/nqPi3PRqHqLgolbQVwkjyfN4yxsyHx3uni25Z1TCT21LR9Zq0FkP4M0k02U73NKbmDeVHwyyQk6XDBfNqt8krsFdR jenkins@tla.msr-inria.inria.fr" >> /home/kuppe/.ssh/authorized_keys
# ec2 keypair to ssh out
echo "##PRIV_KEY##" > /home/kuppe/.ssh/id_rsa
echo "ssh-rsa AAAAB3NzaC1yc2EAAAADAQABAAABAQDY+EiWONhPeuupD26mtePrFDzel5ewHcLow0FfdCNnTyRdXRJVo8iyDROP5YyNfphmgezsRcv62sXAft4sqKoVw14luX9XPjNWDARsTbPOyhBTsJe6qMm/8nZ78zGbL8EEWVE52l3rx2MWYy67VwBaAP5szVVpmj+7VJ4fCh/1Vp9ORgOxwgzdpkt2qx8Tn5qVkjOwxqpGsANsaXLmfdRo9eXFXO845Ok7bytPqdwJsSoB2tRUH8rwHrVPQsJsXYnTQFKf8mhf21uxhdsnHg4jWEk1My/XI+x/mjR8ksQWcpjumVAFw7flMD1ZYBijo3CR+b2GtV4uKTxjf8bbEcBn kuppe@ec2.amazonaws.com" > /home/kuppe/.ssh/id_rsa.pub
chmod 600 /home/kuppe/.ssh/id_rsa

echo "|1|JTnR8MszcgY9ICrrfn1rTYAfhJ0=|ooj9JLHlnXE4odcbzRcEbfrPSgA= ssh-rsa AAAAB3NzaC1yc2EAAAABIwAAAQEAq2A7hRGmdnm9tUDbO9IDSwBK6TbQa+PXYPCPy6rbTrTtw7PHkccKrpp0yVhp5HdEIcKr6pLlVDBfOLX9QUsyCOV0wzfjIJNlGEYsdlLJizHhbn2mUjvSAHQqZETYP81eFzLQNnPHt4EVVUh7VfDESU84KezmD5QlWpXLmvU31/yMf+Se8xhHTvKSCZIFImWwoG6mbUoWf9nzpIoaSjB+weqqUUmpaaasXVal72J+UX2B+2RPW3RcT0eOzQgqlJL3RKrTJvdsjE3JEAvGq3lGHSZXy28G3skua2SmVi/w4yCE6gbODqnTWlg7+wC604ydGXA8VJiS5ap43JXiUFFAaQ==" >> /home/kuppe/.ssh/known_hosts
echo "|1|qEzv5BY1eb03It5QofAvuSqLt+U=|uVPCjIQTi18cTqa6A91/1YUW8EQ= ssh-rsa AAAAB3NzaC1yc2EAAAABIwAAAQEAq2A7hRGmdnm9tUDbO9IDSwBK6TbQa+PXYPCPy6rbTrTtw7PHkccKrpp0yVhp5HdEIcKr6pLlVDBfOLX9QUsyCOV0wzfjIJNlGEYsdlLJizHhbn2mUjvSAHQqZETYP81eFzLQNnPHt4EVVUh7VfDESU84KezmD5QlWpXLmvU31/yMf+Se8xhHTvKSCZIFImWwoG6mbUoWf9nzpIoaSjB+weqqUUmpaaasXVal72J+UX2B+2RPW3RcT0eOzQgqlJL3RKrTJvdsjE3JEAvGq3lGHSZXy28G3skua2SmVi/w4yCE6gbODqnTWlg7+wC604ydGXA8VJiS5ap43JXiUFFAaQ==" >> /home/kuppe/.ssh/known_hosts
echo "|1|b+T9Bgmg1i+3NnURPyDZ5IFKZmE=|/Z4QxMfAee1XLyWPQgPiB4iqMz8= ssh-rsa AAAAB3NzaC1yc2EAAAABIwAAAQEAymaqVw6MX0zpVms76QnTO4jTVMzH9Z0/tKGNfh0LZIkAA6QnXMgCIxo+j7N5zBRIwggh9KuE2UKpL5Q17dQ/ue5rNjfglHU6sZfNjEDcL679BqQISr+PzcVH065e7gpVjfyj6E9we2XLuXSAUSU3yzGyLrneRfKXU7W3GNfGaFszmP6n4QyLaUPBFyMdstaynG4naIxTTZ+VpuaDb5lKpjWqBrnWbzh+/El5wU+DFPnKXAnrQemOZNIVGt15QHoFZoKbaNNP+n+rF6uzxjHrHZJnnyK1xp6lkiSm0WEw7WZGBiCywUDefv+P9CpT4bklWGI5uTgI0m/iJlH5ZU5r3Q==" >> /home/kuppe/.ssh/known_hosts
echo "|1|dDmFUX76/JF4gajz5VzFx+teEO8=|UDBhr6L1q6AOJBL8I2QJXQdepSw= ssh-rsa AAAAB3NzaC1yc2EAAAABIwAAAQEAymaqVw6MX0zpVms76QnTO4jTVMzH9Z0/tKGNfh0LZIkAA6QnXMgCIxo+j7N5zBRIwggh9KuE2UKpL5Q17dQ/ue5rNjfglHU6sZfNjEDcL679BqQISr+PzcVH065e7gpVjfyj6E9we2XLuXSAUSU3yzGyLrneRfKXU7W3GNfGaFszmP6n4QyLaUPBFyMdstaynG4naIxTTZ+VpuaDb5lKpjWqBrnWbzh+/El5wU+DFPnKXAnrQemOZNIVGt15QHoFZoKbaNNP+n+rF6uzxjHrHZJnnyK1xp6lkiSm0WEw7WZGBiCywUDefv+P9CpT4bklWGI5uTgI0m/iJlH5ZU5r3Q==" >> /home/kuppe/.ssh/known_hosts

# fix permission because steps are executed by root
chown -R kuppe:kuppe /home/kuppe
echo "kuppe ALL=(ALL) NOPASSWD: ALL" >> /etc/sudoers

# x2go repository
add-apt-repository ppa:x2go/stable -y

# update package index and install basic packages needed
export DEBIAN_FRONTEND=noninteractive
apt-get update
apt-get upgrade -y
apt-get --no-install-recommends install unzip sysstat apache2 munin munin-node munin-plugins-extra maven git rsync libnet-cidr-perl libnetaddr-ip-perl libxml2-utils xmlstarlet -y
# On Ubuntu 12.10 munin-java-plugins has been renamed to munin-plugins-java
if [ -f /etc/lsb-release ]; then
    source /etc/lsb-release
    if [ $DISTRIB_RELEASE = "12.10" ]; then
        apt-get --no-install-recommends install munin-plugins-java -y
    else
        apt-get --no-install-recommends install munin-java-plugins -y
    fi
fi
# UI/X and dev environment (forked)
apt-get --no-install-recommends install ant openjdk-7-jdk gnome-core gdm gnome-session-fallback firefox visualvm mc libwebkitgtk-1.0-0 tightvncserver xorg x2goserver x2goserver-xsession htop -y &

# clear cached packages to save disk space
apt-get clean

# allow any host to query munin (limited to grid nodes due to AWS fw)
# a munin node restart is triggered by jmx2munin
echo "cidr_allow 0.0.0.0/0" >> /etc/munin/munin-node.conf

# add maven and ant to the path
echo "export MAVEN_HOME=/opt/apache-maven/
export PATH=$PATH:/opt/apache-maven/bin
" > /etc/profile.d/java.sh

# create instance-local folder to keep TLC states/
mkdir -p /mnt/tlc
chown kuppe:kuppe /mnt/tlc

mkdir -p /mnt/kuppe
mkdir -p /home/kuppe/git
chown -R kuppe:kuppe /home/kuppe/

# clone git repo for eclipse to pick it up easily
sudo -u kuppe /usr/bin/git clone git@github.com:lemmy/tlc-perf.git /home/kuppe/git/ec2
sudo -u kuppe /usr/bin/git config --global user.email tlaplus.net@lemmster.de
sudo -u kuppe /usr/bin/git config --global user.name "Markus Alexander Kuppe"

# Dump stats to tla.msr-inria.inria.fr
# disabled for the moment: 
# - only useful for multi-day jobs, otherwise put too much load on tla.msr...
# - stats are collected once at the end explicitly)
#echo "MAILTO=root
#*/240 * * * * root /usr/local/bin/rrdbackup.sh
#" > /etc/cron.d/rrdbackup

echo "#!/bin/bash
# Either empty or set externally as first parameter
BUILD_ID=\${1-\"\"}
# Dump process list
ps axu|grep java|grep -v grep >> /var/lib/munin/ps.txt
# Convert from rrd to xml
cd /var/lib/munin/
for f in */*.rrd; do rrdtool dump \${f} > \${f/rrd/xml}; done
# Remove stats we don't need
for f in `find -L . -name *apache*.xml`; do rm \${f}; done
for f in `find -L . -name *irqstats*.xml`; do rm \${f}; done
# Do a little name mangling (-L causes it to follow symlinks)
for f in `find -L . -name *jmx2munin_org_vafer*.xml`; do mv \${f} \${f/jmx2munin_org_vafer_jmx_contention_/}; done
for f in `find -L . -name *jmx2munin_tlc2_tool_fp_*.xml`; do mv \${f} \${f/jmx2munin_tlc2_tool_fp_/}; done
for f in `find -L . -name *mx2munin_tlc2_tool_*.xml`; do mv \${f} \${f/jmx2munin_tlc2_tool_/}; done
for f in `find -L . -name *jmx_*.xml`; do mv \${f} \${f/jmx_/}; done
for f in `find -L . -name *.ec2.internal*.xml`; do mv \${f} \${f/.ec2.internal/}; done
for f in `find -L . -name *tlc-*.rrd`; do mv \${f} \${f/tlc-/}; done
for f in `find -L . -name *-g.rrd`; do mv \${f} \${f/-g/}; done
for f in `find -L . -name ModelChecker__averageblockcnt-tlc2_tool_modelchecker_averageblockcnt.rrd`; do mv \${f} \${f/__averageblockcnt-tlc2_tool_modelchecker/}; done
for f in `find -L . -name ModelChecker__distinctstatesgeneratedperminute-tlc2_tool_modelchecker*.rrd`; do mv \${f} \${f/__distinctstatesgeneratedperminute-tlc2_tool_modelchecker/}; done
for f in `find -L . -name ModelChecker__distinctstatesgenerated-tlc2_tool_modelchecker_distinctstatesgenerated.rrd`; do mv \${f} \${f/__distinctstatesgenerated-tlc2_tool_modelchecker/}; done
for f in `find -L . -name ModelChecker__progress-tlc2_tool_modelchecker_progress.rrd`; do mv \${f} \${f/__progress-tlc2_tool_modelchecker/}; done
for f in `find -L . -name ModelChecker__statequeuesize-tlc2_tool_modelchecker_statequeuesize.rrd`; do mv \${f} \${f/__statequeuesize-tlc2_tool_modelchecker/}; done
for f in `find -L . -name ModelChecker__statesgeneratedperminute-tlc2_tool_modelchecker_statesgeneratedperminute.rrd`; do mv \${f} \${f/__statesgeneratedperminute-tlc2_tool_modelchecker/}; done
for f in `find -L . -name ModelChecker__statesgenerated-tlc2_tool_modelchecker_statesgenerated.rrd`; do mv \${f} \${f/__statesgenerated-tlc2_tool_modelchecker/}; done
for f in `find -L . -name ModelChecker__workercount-tlc2_tool_modelchecker_workercount.rrd`; do mv \${f} \${f/__workercount-tlc2_tool_modelchecker/}; done

for f in `find -L . -name *__bucketcapacity-tlc2_tool_fp_diskfpset*.rrd`; do mv \${f} \${f/__bucketcapacity-tlc2_tool_fp_diskfpset/}; done
for f in `find -L . -name *__checkpointmark-tlc2_tool_fp_diskfpset*.rrd`; do mv \${f} \${f/__checkpointmark-tlc2_tool_fp_diskfpset/}; done
for f in `find -L . -name *__collisionbucketcnt-tlc2_tool_fp_diskfpset*.rrd`; do mv \${f} \${f/__collisionbucketcnt-tlc2_tool_fp_diskfpset/}; done
for f in `find -L . -name *__collisionratio-tlc2_tool_fp_diskfpset*.rrd`; do mv \${f} \${f/__collisionratio-tlc2_tool_fp_diskfpset/}; done
for f in `find -L . -name *__diskhitcnt-tlc2_tool_fp_diskfpset*.rrd`; do mv \${f} \${f/__diskhitcnt-tlc2_tool_fp_diskfpset/}; done
for f in `find -L . -name *__disklookupcnt-tlc2_tool_fp_diskfpset*.rrd`; do mv \${f} \${f/__disklookupcnt-tlc2_tool_fp_diskfpset/}; done
for f in `find -L . -name *__diskseekcache-tlc2_tool_fp_diskfpset*.rrd`; do mv \${f} \${f/__diskseekcache-tlc2_tool_fp_diskfpset/}; done
for f in `find -L . -name *__diskseekcnt-tlc2_tool_fp_diskfpset*.rrd`; do mv \${f} \${f/__diskseekcnt-tlc2_tool_fp_diskfpset/}; done
for f in `find -L . -name *__diskseekrate-tlc2_tool_fp_diskfpset*.rrd`; do mv \${f} \${f/__diskseekrate-tlc2_tool_fp_diskfpset/}; done
for f in `find -L . -name *__diskwritecnt-tlc2_tool_fp_diskfpset*.rrd`; do mv \${f} \${f/__diskwritecnt-tlc2_tool_fp_diskfpset/}; done
for f in `find -L . -name *__filecnt-tlc2_tool_fp_diskfpset*.rrd`; do mv \${f} \${f/__filecnt-tlc2_tool_fp_diskfpset/}; done
for f in `find -L . -name *__flushtime-tlc2_tool_fp_diskfpset*.rrd`; do mv \${f} \${f/__flushtime-tlc2_tool_fp_diskfpset/}; done
for f in `find -L . -name *__growdiskmark-tlc2_tool_fp_diskfpset*.rrd`; do mv \${f} \${f/__growdiskmark-tlc2_tool_fp_diskfpset/}; done
for f in `find -L . -name *__indexcnt-tlc2_tool_fp_diskfpset*.rrd`; do mv \${f} \${f/__indexcnt-tlc2_tool_fp_diskfpset/}; done
for f in `find -L . -name *__loadfactor-tlc2_tool_fp_diskfpset*.rrd`; do mv \${f} \${f/__loadfactor-tlc2_tool_fp_diskfpset/}; done
for f in `find -L . -name *__maxtblcnt-tlc2_tool_fp_diskfpset*.rrd`; do mv \${f} \${f/__maxtblcnt-tlc2_tool_fp_diskfpset/}; done
for f in `find -L . -name *__memhitcnt-tlc2_tool_fp_diskfpset*.rrd`; do mv \${f} \${f/__memhitcnt-tlc2_tool_fp_diskfpset/}; done
for f in `find -L . -name *__overallcapacity-tlc2_tool_fp_diskfpset*.rrd`; do mv \${f} \${f/__overallcapacity-tlc2_tool_fp_diskfpset/}; done
for f in `find -L . -name *__readerwritercnt-tlc2_tool_fp_diskfpset*.rrd`; do mv \${f} \${f/__readerwritercnt-tlc2_tool_fp_diskfpset/}; done
for f in `find -L . -name *__sizeof-tlc2_tool_fp_diskfpset*.rrd`; do mv \${f} \${f/__sizeof-tlc2_tool_fp_diskfpset/}; done
for f in `find -L . -name *__tblcapacity-tlc2_tool_fp_diskfpset*.rrd`; do mv \${f} \${f/__tblcapacity-tlc2_tool_fp_diskfpset/}; done
for f in `find -L . -name *__tblcnt-tlc2_tool_fp_diskfpset*.rrd`; do mv \${f} \${f/__tblcnt-tlc2_tool_fp_diskfpset/}; done
for f in `find -L . -name *__tblload-tlc2_tool_fp_diskfpset*.rrd`; do mv \${f} \${f/__tblload-tlc2_tool_fp_diskfpset/}; done

for f in `find -L . -name *__blockedtime-org_vafer_contention_tlcworkerthread*.rrd`; do mv \${f} \${f/__blockedtime-org_vafer_contention_tlcworkerthread/}; done
for f in `find -L . -name *__waitedtime-org_vafer_contention_tlcworkerthread*.rrd`; do mv \${f} \${f/__waitedtime-org_vafer_contention_tlcworkerthread/}; done

# sync
sudo -u kuppe ssh ec2perf@tla.msr-inria.inria.fr mkdir -p /home/kuppe/rrdtool/\$BUILD_ID
sudo -u kuppe rsync --exclude=*.rrd -az -e ssh /var/lib/munin/ ec2perf@tla.msr-inria.inria.fr:~/rrdtool/\$BUILD_ID/\`hostname\`
sudo -u kuppe rsync -az -e ssh /var/cache/munin/ ec2perf@tla.msr-inria.inria.fr:~/rrdtool/\$BUILD_ID/\`hostname\`
" > /usr/local/bin/rrdbackup.sh
chmod +x /usr/local/bin/rrdbackup.sh

# install TLC munin extensions (needs ec2 repo present)
cd /mnt/kuppe/git/ec2/tools/jmx2munin
./install.sh

# Last but not least mark the completion of this script
mkdir /tmp/data-file-init-complete/

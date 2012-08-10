#!/bin/bash
#
# To run this script the ec2-ami-tools have to be installed on your system. 
# Afterwards the following command will create a new instance and execute this script right after system startup. 
# It should be good for TLC development afterwards.
#
# ec2-run-instances -m --key markus@kuppe.org --instance-type m2.4xlarge --user-data-file /path/to/ProvisionEC2.sh ami-c162a9a8
#

# format and mount second ephemeral disk
/sbin/mkfs.ext4 /dev/xvbc
mkdir /mnt2
mount /dev/xvdc /mnt2
chmod 777 /mnt2

# switch to mount to use the instance ephemeral storage rather than ESB
cd /mnt

# download non pkg mgmt provided maven3 tool in background
(wget -q http://apache.osuosl.org/maven/binaries/apache-maven-3.0.4-bin.tar.gz && cd /opt && tar xfz /mnt/apache-maven-3.0.4-bin.tar.gz) &

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
echo "-----BEGIN RSA PRIVATE KEY-----
MIIEowIBAAKCAQEA2PhIljjYT3rrqQ9uprXj6xQ83peXsB3C6MNBX3QjZ08kXV0S
VaPIsg0Tj+WMjX6YZoHs7EXL+trFwH7eLKiqFcNeJbl/Vz4zVgwEbE2zzsoQU7CX
uqjJv/J2e/Mxmy/BBFlROdpd68djFmMuu1cAWgD+bM1VaZo/u1SeHwof9VafTkYD
scIM3aZLdqsfE5+alZIzsMaqRrADbGly5n3UaPXlxVzvOOTpO28rT6ncCbEqAdrU
VB/K8B61T0LCbF2J00BSn/JoX9tbsYXbJx4OI1hJNTMv1yPsf5o0fJLEFnKY7plQ
BcO35TA9WWAYo6Nwkfm9hrVeLik8Y3/G2xHAZwIDAQABAoIBAEVMZ8KzPUOFeydw
KmNMzRMUT6y4tlYl6070rjiSm4wvlunLBEQeH8ferVTUeGPo/zweW1HLqS7iGS82
VjflVw3EbJmX+bgfwb3F8NO2ratqlnRkftG7f1SzWGyWbE2onvmInYzg1gaslFVe
MFrdmtskXh7aJmGoRprKmAZJ8ZMmFJVjJAfRPud59kcWMy8p6vopTnMvD0erAP5i
eVhq9uzEpeQnNewxURSjigCXJW61UF1rWbNbAd6sb/kIYW3nit7g0yAYBfp0u+ay
dbHampIrxLO2czzOtkzn1AMZsP1l87Bpan0BorxnuBMUe4bXOeLoXrh24yYwr4Lm
3PVt0mECgYEA/njoI6002yai8sAeO+v9dSJcBJyG41mx8e4xuNof39Wq7UEUdBFa
9Jf6G1FhgW0y8vD5jOKjWGpNvPpWVZ+Egd/OcYBDqanhV50NVvl7+OIMy/qZHj46
dWDFmd5WYaacock5E+brV4xyPCsE3Pq8N0qvy6WmvyygpFZj+Jr/5o0CgYEA2kW9
crGRLCEPzL0/IAs/Ae7UbwMPRFL2n9WMBQ6EBf6ICirLXc8/PR1PaRNabgKOXsF8
XgLq5PnHM9mKzIJhEagP9yBtQ6VcBf6sH1mC0Vgcr6wO88PXFQo1gP85WbD2MMtM
07Hl7jDLD3sB+HOYZ3tpCcp8NRSQyrBToB1mb8MCgYBpfXW+VG806i9isoHWFV5c
0IGU586DMQuzXyr9lm7gO5NAB1qTQx6Rhu8HpBTnsn0MeRj6bnmIjYjsblqb5CTq
Mf1C0Ak8rE/eIh0FkSbzZcIoTRpsjx9syVEhGCp3ELqd1uzycyfcgzxX9P1vHgIo
aa22nlUhqz5s4eNPi/HJgQKBgEa69LIW8lkfeZQ5+xuyKT/CGdrDXg4g6ERRGeeF
laivm3vX9EC46OAwAEynddVSRLpV7qw0O9PpUPDvXLf6w+PJ1yqYum+CRTi4FySt
h+O4rssKcWnym175CO99RSNYYd7b8lBjRIQUEak5jiDprIhUCGygzfERcf4Md3za
KhirAoGBAMATt4LvEhVizVxQyv3Y0AHFkA5BD2a/rb0N5IKA3C3hBdjzhCcpN1CH
9SDc4bC6r2rNVpPsfQmzrd7SBeNfGQt4LlqM+T8K4tG/XBv/qzJepNovaktXc+Kk
Ql9HA1KsWKcIixTRgHsG7XmtW5tETAQgi2n2oz/YbyQcNDQQCnSx
-----END RSA PRIVATE KEY-----
" > /home/kuppe/.ssh/id_rsa
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
apt-get --no-install-recommends install ant openjdk-7-jdk visualvm openjdk-6-jdk juju unzip mc htop sysstat apache2 munin munin-node munin-java-plugins munin-plugins-extra git sshfs rsync libnet-cidr-perl libnetaddr-ip-perl libxml2-utils xmlstarlet -y
# if UI/X needed
apt-get --no-install-recommends install gnome-core gdm gnome-session-fallback firefox libwebkitgtk-1.0-0 tightvncserver xorg x2goserver x2goserver-xsession -y

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
echo "MAILTO=root
*/120 * * * * root ps axu|grep java|grep -v grep >> /var/lib/munin/ps.txt
*/120 * * * * root /bin/bash -c 'cd /var/lib/munin/tlc/ && for f in *.rrd; do rrdtool dump \${f} > \${f/rrd/xml}; done'
*/120 * * * * root /bin/bash -c 'cd /var/lib/munin/ec2.internal/ && for f in *.rrd; do rrdtool dump \${f} > \${f/rrd/xml}; done'
*/120 * * * * kuppe rsync --exclude=*.rrd -avz -e ssh /var/lib/munin/ kuppe@tla.msr-inria.inria.fr:~/rrdtool/`hostname`
*/120 * * * * kuppe rsync -avz -e ssh /var/cache/munin/ kuppe@tla.msr-inria.inria.fr:~/rrdtool/`hostname`
" > /etc/cron.d/rrdbackup

# install TLC munin extensions (needs ec2 repo present)
cd /mnt/kuppe/git/ec2/tools/jmx2munin
./install.sh


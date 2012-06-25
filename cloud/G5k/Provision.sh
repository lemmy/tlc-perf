#!/bin/bash

# allow user mkuppe to use sudo without password
sed -i 's/%sudo ALL=(ALL) ALL/%sudo ALL=(ALL) NOPASSWD: ALL/g' /etc/sudoers
usermod -G sudo -a mkuppe

# update package index and install basic packages needed
export DEBIAN_FRONTEND=noninteractive
apt-get update
apt-get upgrade -y
apt-get --no-install-recommends install ant openjdk-6-jdk unzip mc htop sysstat apache2 munin munin-node munin-java-plugins munin-plugins-extra git sshfs rsync libnet-cidr-perl libnetaddr-ip-perl xmlstartlet xmllint -y

# clear cached packages to save disk space
apt-get clean

# allow any host to query munin (limited to grid nodes due to external fw)
# a munin node restart is triggered by jmx2munin
echo "cidr_allow 0.0.0.0/0" >> /etc/munin/munin-node.conf

# install TLC munin extensions
../../tools/jmx2munin/install.sh

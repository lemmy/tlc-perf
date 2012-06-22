#!/bin/bash

# allow user mkuppe to use sudo without password
sed -i 's/%sudo ALL=(ALL) ALL/%sudo ALL=(ALL) NOPASSWD: ALL/g' /etc/sudoers
usermod -G sudo -a mkuppe

# update package index and install basic packages needed
export DEBIAN_FRONTEND=noninteractive
apt-get update
apt-get upgrade -y
apt-get --no-install-recommends install ant openjdk-6-jdk unzip mc htop sysstat apache2 munin munin-node munin-java-plugins munin-plugins-extra git sshfs rsync -y

# clear cached packages to save disk space
apt-get clean

# install TLC munin extensions
../../tools/jmx2munin/install.sh

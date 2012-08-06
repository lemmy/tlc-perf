#!/bin/bash

# Install jenkins latest
wget -q -O - http://pkg.jenkins-ci.org/debian-stable/jenkins-ci.org.key | apt-key add -
sh -c 'echo deb http://pkg.jenkins-ci.org/debian-stable binary/ > /etc/apt/sources.list.d/jenkins.list'
aptitude update
aptitude install jenkins -y

# Set jenkins prefix which matches the URL under which apache is going to proxy jenkins
sed -i 's/PREFIX=\/jenkins/PREFIX=\/build/g' /etc/default/jenkins
sed -i 's/JENKINS_ARGS="--webroot=\/var\/cache\/jenkins\/war --httpPort=$HTTP_PORT --ajp13Port=$AJP_PORT"/JENKINS_ARGS="--webroot=\/var\/cache\/jenkins\/war --httpPort=$HTTP_PORT --ajp13Port=$AJP_PORT --prefix=$PREFIX"/g' /etc/default/jenkins

# Set jenkins home to reside on node local storage
mkdir -p /mnt/jenkins/plugins/
sed -i 's/JENKINS_HOME=\/var\/lib\/jenkins/JENKINS_HOME=\/mnt\/jenkins/g' /etc/default/jenkins

# Install necessary plugins
cd /mnt/jenkins/plugins
wget -q http://updates.jenkins-ci.org/latest/thinBackup.hpi
wget -q http://updates.jenkins-ci.org/latest/git.hpi
wget -q http://updates.jenkins-ci.org/latest/scm-sync-configuration.hpi
wget -q http://updates.jenkins-ci.org/latest/subversion.hpi
wget -q http://updates.jenkins-ci.org/latest/xvnc.hpi
wget -q http://updates.jenkins-ci.org/latest/ec2.hpi
wget -q http://updates.jenkins-ci.org/latest/ws-cleanup.hpi
wget -q http://updates.jenkins-ci.org/latest/bugzilla.hpi
wget -q http://updates.jenkins-ci.org/latest/promoted-builds.hpi
cd -

# Finally make sure everything belong to jenkins user
chown -R jenkins:nogroup /mnt/jenkins

# Apply jenkins conf somehow?!
echo "TODO!!!
- ThinBackup
- Jenkins plugings"

# "Reuse" tla git repo provisioned for user kuppe
# Jenkins consumes it as file:///home/kuppe/tla.git
ln -s /home/kuppe/git/tla/ /home/kuppe/tla.git

# Restart jenkins to pick up config changes
service jenkins restart

#
# Activate Apache2 proxy modules
a2enmod proxy
a2enmod proxy_http

# Set up Apache to proxy the Jenkins server under build/ URL
echo "
    # Build server based on jenkins serverd by built-in jetty webserver
    ProxyPass         /build  http://localhost:8080/build
    ProxyPassReverse  /build  http://localhost:8080/build
    ProxyRequests     Off

    # Local reverse proxy authorization override
    # Most unix distribution deny proxy by default (ie /etc/apache2/mods-enabled/proxy.conf in Ubuntu)
    <Proxy http://localhost:8080/build*>
        Order deny,allow
        Allow from all
    </Proxy>" > /etc/apache2/conf.d/jenkins

# Restart Apache to pick up config changes
service apache2 restart


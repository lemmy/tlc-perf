#!/bin/bash
##
## This script assumes that the base (linux) machine has been provisioned with the script in EC2/Provision.sh.
##


## Install jenkins LTS
wget -q -O - http://pkg.jenkins-ci.org/debian-stable/jenkins-ci.org.key | apt-key add -
sh -c 'echo deb http://pkg.jenkins-ci.org/debian-stable binary/ > /etc/apt/sources.list.d/jenkins.list'
apt-get update
export DEBIAN_FRONTEND=noninteractive
apt-get install jenkins -y

## Install Javas still referred to by Jenkins configuration
apt-get install oracle-java6-installer oracle-java7-installer oracle-java8-installer oracle-java8-set-default -y

## Stop jenkins to tweak configuration
service jenkins stop

## Set jenkins prefix which matches the URL under which apache is going to proxy jenkins
sed -i 's/PREFIX=\/jenkins/PREFIX=\/build/g' /etc/default/jenkins
sed -i 's/JENKINS_ARGS="--webroot=\/var\/cache\/jenkins\/war --httpPort=$HTTP_PORT --ajp13Port=$AJP_PORT"/JENKINS_ARGS="--webroot=\/var\/cache\/jenkins\/war --httpPort=$HTTP_PORT --ajp13Port=$AJP_PORT --prefix=$PREFIX"/g' /etc/default/jenkins

## Set jenkins home to reside on node local storage
mkdir -p /mnt/jenkins/plugins/scm-sync-configuration/checkoutConfiguration
sed -i 's/JENKINS_HOME=\/var\/lib\/jenkins/JENKINS_HOME=\/mnt\/jenkins/g' /etc/default/jenkins

## Install necessary plugins.
## This list might not be uptodate when a plugin's dependency has changed.
## Check the embedded MANIFEST.MF for the list of dependency and provide
## the complete transitive closure.
mkdir /mnt/jenkins/plugins -p
cd /mnt/jenkins/plugins
wget -q https://updates.jenkins-ci.org/latest/git.hpi
wget -q https://updates.jenkins-ci.org/latest/git-client.hpi

wget -q https://updates.jenkins-ci.org/latest/github-api.hpi
wget -q https://updates.jenkins-ci.org/latest/github.hpi

wget -q https://updates.jenkins-ci.org/latest/token-macro.hpi
wget -q https://updates.jenkins-ci.org/latest/build-timeout.hpi

wget -q https://updates.jenkins-ci.org/latest/scm-sync-configuration.hpi
wget -q https://updates.jenkins-ci.org/latest/xvnc.hpi

wget -q https://updates.jenkins-ci.org/latest/ec2.hpi
wget -q https://updates.jenkins-ci.org/latest/node-iterator-api.hpi

wget -q https://updates.jenkins-ci.org/latest/ws-cleanup.hpi
wget -q https://updates.jenkins-ci.org/latest/promoted-builds.hpi
wget -q https://updates.jenkins-ci.org/latest/jacoco.hpi
wget -q https://updates.jenkins-ci.org/latest/rebuild.hpi
wget -q https://updates.jenkins-ci.org/latest/postbuild-task.hpi
wget -q https://updates.jenkins-ci.org/latest/postbuildscript.hpi
cd -

## Finally make sure everything belong to jenkins user before we restart jenkins
chown -R jenkins:nogroup /mnt/jenkins

## Setup public part of ssh key
mkdir -p /var/lib/jenkins/.ssh
echo "ssh-rsa AAAAB3NzaC1yc2EAAAADAQABAAABAQDZWGzBB+uHHtLOw0PsizjW4YpHs4u+8Wo4Exy+Yr+iYcVCNzAcR8e+ixpve14FaVN9ia7Trjd8xC8j/AWiQ+oMHXdJZQNrfKUtUxebSxA0yqlE3WXSjq+uAyRUT8czc5aM8h93iVz5AZwbUPy6ayxFr0PrVE/XmA+ZSAZ2pbPOg/KVZhqMILznCwhQ5lyUsIMSdZNIUlZH5+347zEvhJFhoPy95c4qs5qWvEaXD9Dxu/wCHqIv0KAKC4dxr+/nqPi3PRqHqLgolbQVwkjyfN4yxsyHx3uni25Z1TCT21LR9Zq0FkP4M0k02U73NKbmDeVHwyyQk6XDBfNqt8krsFdR jenkins@tla.msr-inria.inria.fr" > /var/lib/jenkins/.ssh/id_rsa.pub

## Prepare private part
touch /var/lib/jenkins/.ssh/id_rsa
chmod 0600 /var/lib/jenkins/.ssh/id_rsa
echo "Manually add the PRIVATE key to Jenkin's ~/.ssh/id_rsa!!!"

## Append bitbuckets public key (possibly changed in the meantime)
echo "|1|wpDZ8Fn4EonrKquj/RD5MzTGnHw=|4+5YvIJwWbghz+AqWI4iOwFEAFQ= ssh-rsa AAAAB3NzaC1yc2EAAAABIwAAAQEAubiN81eDcafrgMeLzaFPsw2kNvEcqTKl/VqLat/MaB33pZy0y3rJZtnqwR2qOOvbwKZYKiEO1O6VqNEBxKvJJelCq0dTXWT5pbO2gDXC6h6QDXCaHo6pOHGPUy+YBaGQRGuSusMEASYiWunYN0vCAI8QaXnWMXNMdFP3jHAJH0eDsoiGnLPBlBp4TNm6rYI74nMzgz3B9IikW4WVK+dc8KZJZWYjAuORU3jc1c/NPskD2ASinf8v3xnfXeukU0sJ5N6m5E8VLjObPEO+mN2t/FZTMZLiFqPWc/ALSqnMnnhwrNi2rbfg/rd/IpL8Le3pSBne8+seeFVBoGqzHM9yXw==" >> /var/lib/jenkins/.ssh/known_hosts
echo "|1|FqajFz2ZE6BtAHHbjI3U9koeJS4=|z48S4B41iYY4Tem6miLN/umPXRY= ssh-rsa AAAAB3NzaC1yc2EAAAABIwAAAQEAubiN81eDcafrgMeLzaFPsw2kNvEcqTKl/VqLat/MaB33pZy0y3rJZtnqwR2qOOvbwKZYKiEO1O6VqNEBxKvJJelCq0dTXWT5pbO2gDXC6h6QDXCaHo6pOHGPUy+YBaGQRGuSusMEASYiWunYN0vCAI8QaXnWMXNMdFP3jHAJH0eDsoiGnLPBlBp4TNm6rYI74nMzgz3B9IikW4WVK+dc8KZJZWYjAuORU3jc1c/NPskD2ASinf8v3xnfXeukU0sJ5N6m5E8VLjObPEO+mN2t/FZTMZLiFqPWc/ALSqnMnnhwrNi2rbfg/rd/IpL8Le3pSBne8+seeFVBoGqzHM9yXw==" >> /var/lib/jenkins/.ssh/known_hosts

chown -R jenkins:nogroup /var/lib/jenkins/.ssh/

## Link /usr/bin/git to /usr/local/bin/git
## (current squeeze based Jenkins on tla.msr... uses a manually installed version to be compatible with codeplex)
ln -s /usr/bin/git /usr/local/bin/git

## Restart jenkins to pick up config changes
service jenkins restart

## "Reuse" tla git repo provisioned for user kuppe
## Jenkins consumes it as file:///home/kuppe/tla.git
ln -s /home/kuppe/git/tla/ /home/kuppe/tla.git

##
## Activate Apache2 proxy modules and SSL
a2enmod proxy
a2enmod proxy_http
a2enmod ssl

## Set up SSL to protect network communication
echo "TODO!!! (where to get the private key from)"

## Set up Apache to proxy the Jenkins server under build/ URL
echo "
<IfModule mod_ssl.c>
<VirtualHost _default_:443>
    ServerAdmin webmaster@localhost

    DocumentRoot /var/www
    <Directory />
        Options FollowSymLinks
        AllowOverride None
    </Directory>
    <Directory /var/www/>
        Options Indexes FollowSymLinks MultiViews
        AllowOverride None
        Order allow,deny
        allow from all
    </Directory>

    SSLEngine on
    SSLCertificateFile    /etc/ssl/private/tla.msr-inria.inria.fr.crt
    SSLCertificateKeyFile /etc/ssl/private/tla.msr-inria.inria.fr.key
    SSLCertificateChainFile /etc/ssl/private/tla.msr-inria.inria.fr.chain

    ProxyRequests     Off
    ProxyPreserveHost On
    AllowEncodedSlashes off

    <Proxy http://localhost:8080/build*>
        Order deny,allow
        Allow from all
    </Proxy>

    ProxyPass         /build  http://localhost:8080/build nocanon
    ProxyPassReverse  /build  http://localhost:8080/build
    ProxyPassReverse  /build  http://tla.msr-inria.inria.fr/build
</VirtualHost>
</IfModule>" > /etc/apache2/sites-available/jenkins.conf

a2ensite jenkins

## Remove munin config created by main deployment script EC2/Provision.sh
rm -r /etc/apache2/conf-enabled/munin.conf

echo "
-----BEGIN CERTIFICATE-----
MIIEmDCCA4CgAwIBAgIQS8gUAy8H+mqk8Nop32F5ujANBgkqhkiG9w0BAQUFADCB
lzELMAkGA1UEBhMCVVMxCzAJBgNVBAgTAlVUMRcwFQYDVQQHEw5TYWx0IExha2Ug
Q2l0eTEeMBwGA1UEChMVVGhlIFVTRVJUUlVTVCBOZXR3b3JrMSEwHwYDVQQLExho
dHRwOi8vd3d3LnVzZXJ0cnVzdC5jb20xHzAdBgNVBAMTFlVUTi1VU0VSRmlyc3Qt
SGFyZHdhcmUwHhcNMDkwNTE4MDAwMDAwWhcNMjAwNTMwMTA0ODM4WjA2MQswCQYD
VQQGEwJOTDEPMA0GA1UEChMGVEVSRU5BMRYwFAYDVQQDEw1URVJFTkEgU1NMIENB
MIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEAw+NIxC9cwcupmf0booNd
ij2tOtDipEMfTQ7+NSUwpWkbxOjlwY9UfuFqoppcXN49/ALOlrhfj4NbzGBAkPjk
tjolnF8UUeyx56+eUKExVccCvaxSin81joL6hK0V/qJ/gxA6VVOULAEWdJRUYyij
8lspPZSIgCDiFFkhGbSkmOFg5vLrooCDQ+CtaPN5GYtoQ1E/iptBhQw1jF218bbl
p8ODtWsjb9Sl61DllPFKX+4nSxQSFSRMDc9ijbcAIa06Mg9YC18em9HfnY6pGTVQ
L0GprTvG4EWyUzl/Ib8iGodcNK5Sbwd9ogtOnyt5pn0T3fV/g3wvWl13eHiRoBS/
fQIDAQABo4IBPjCCATowHwYDVR0jBBgwFoAUoXJfJhsomEOVXQc31YWWnUvSw0Uw
HQYDVR0OBBYEFAy9k2gM896ro0lrKzdXR+qQ47ntMA4GA1UdDwEB/wQEAwIBBjAS
BgNVHRMBAf8ECDAGAQH/AgEAMBgGA1UdIAQRMA8wDQYLKwYBBAGyMQECAh0wRAYD
VR0fBD0wOzA5oDegNYYzaHR0cDovL2NybC51c2VydHJ1c3QuY29tL1VUTi1VU0VS
Rmlyc3QtSGFyZHdhcmUuY3JsMHQGCCsGAQUFBwEBBGgwZjA9BggrBgEFBQcwAoYx
aHR0cDovL2NydC51c2VydHJ1c3QuY29tL1VUTkFkZFRydXN0U2VydmVyX0NBLmNy
dDAlBggrBgEFBQcwAYYZaHR0cDovL29jc3AudXNlcnRydXN0LmNvbTANBgkqhkiG
9w0BAQUFAAOCAQEATiPuSJz2hYtxxApuc5NywDqOgIrZs8qy1AGcKM/yXA4hRJML
thoh45gBlA5nSYEevj0NTmDa76AxTpXv8916WoIgQ7ahY0OzUGlDYktWYrA0irkT
Q1mT7BR5iPNIk+idyfqHcgxrVqDDFY1opYcfcS3mWm08aXFABFXcoEOUIEU4eNe9
itg5xt8Jt1qaqQO4KBB4zb8BG1oRPjj02Bs0ec8z0gH9rJjNbUcRkEy7uVvYcOfV
r7bMxIbmdcCeKbYrDyqlaQIN4+mitF3A884saoU4dmHGSYKrUbOCprlBmCiY+2v+
ihb/MX5UR6g83EMmqZsFt57ANEORMNQywxFa4Q==
-----END CERTIFICATE-----

-----BEGIN CERTIFICATE-----
MIIEPDCCAySgAwIBAgIQSEus8arH1xND0aJ0NUmXJTANBgkqhkiG9w0BAQUFADBv
MQswCQYDVQQGEwJTRTEUMBIGA1UEChMLQWRkVHJ1c3QgQUIxJjAkBgNVBAsTHUFk
ZFRydXN0IEV4dGVybmFsIFRUUCBOZXR3b3JrMSIwIAYDVQQDExlBZGRUcnVzdCBF
eHRlcm5hbCBDQSBSb290MB4XDTA1MDYwNzA4MDkxMFoXDTIwMDUzMDEwNDgzOFow
gZcxCzAJBgNVBAYTAlVTMQswCQYDVQQIEwJVVDEXMBUGA1UEBxMOU2FsdCBMYWtl
IENpdHkxHjAcBgNVBAoTFVRoZSBVU0VSVFJVU1QgTmV0d29yazEhMB8GA1UECxMY
aHR0cDovL3d3dy51c2VydHJ1c3QuY29tMR8wHQYDVQQDExZVVE4tVVNFUkZpcnN0
LUhhcmR3YXJlMIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEAsffDOD+0
qH/POYJRZ9Btn9L/WPPnnyvsDYlUmbk4mRb34CF5SMK7YXQSlh08anLVPBBnOjnt
KxPNZuuVCTOkbJex6MbswXV5nEZejavQav25KlUXEFSzGfCa9vGxXbanbfvgcRdr
ooj7AN/+GjF3DJoBerEy4ysBBzhuw6VeI7xFm3tQwckwj9vlK3rTW/szQB6g1ZgX
vIuHw4nTXaCOsqqq9o5piAbF+okh8widaS4JM5spDUYPjMxJNLBpUb35Bs1orWZM
vD6sYb0KiA7I3z3ufARMnQpea5HW7sftKI2rTYeJc9BupNAeFosU4XZEA39jrOTN
SZzFkvSrMqFIWwIDAQABo4GqMIGnMB8GA1UdIwQYMBaAFK29mHo0tCb3+sQmVO8D
veAky1QaMB0GA1UdDgQWBBShcl8mGyiYQ5VdBzfVhZadS9LDRTAOBgNVHQ8BAf8E
BAMCAQYwDwYDVR0TAQH/BAUwAwEB/zBEBgNVHR8EPTA7MDmgN6A1hjNodHRwOi8v
Y3JsLnVzZXJ0cnVzdC5jb20vQWRkVHJ1c3RFeHRlcm5hbENBUm9vdC5jcmwwDQYJ
KoZIhvcNAQEFBQADggEBADzse+Cuow6WbTDXhcbSaFtFWoKmNA+wyZIjXhFtCBGy
dAkjOjUlc1heyrl8KPpH7PmgA1hQtlPvjNs55Gfp2MooRtSn4PU4dfjny1y/HRE8
akCbLURW0/f/BSgyDBXIZEWT6CEkjy3aeoR7T8/NsiV8dxDTlNEEkaglHAkiD31E
NREU768A/l7qX46w2ZJZuvwTlqAYAVbO2vYoC7Gv3VxPXLLzj1pxz+0YrWOIHY6V
9+qV5x+tkLiECEeFfyIvGh1IMNZMCNg3GWcyK+tc0LL8blefBDVekAB+EcfeEyrN
pG1FJseIVqDwavfY5/wnfmcI0L36tsNhAgFlubgvz1o=
-----END CERTIFICATE-----

-----BEGIN CERTIFICATE-----
MIIENjCCAx6gAwIBAgIBATANBgkqhkiG9w0BAQUFADBvMQswCQYDVQQGEwJTRTEU
MBIGA1UEChMLQWRkVHJ1c3QgQUIxJjAkBgNVBAsTHUFkZFRydXN0IEV4dGVybmFs
IFRUUCBOZXR3b3JrMSIwIAYDVQQDExlBZGRUcnVzdCBFeHRlcm5hbCBDQSBSb290
MB4XDTAwMDUzMDEwNDgzOFoXDTIwMDUzMDEwNDgzOFowbzELMAkGA1UEBhMCU0Ux
FDASBgNVBAoTC0FkZFRydXN0IEFCMSYwJAYDVQQLEx1BZGRUcnVzdCBFeHRlcm5h
bCBUVFAgTmV0d29yazEiMCAGA1UEAxMZQWRkVHJ1c3QgRXh0ZXJuYWwgQ0EgUm9v
dDCCASIwDQYJKoZIhvcNAQEBBQADggEPADCCAQoCggEBALf3GjPm8gAELTngTlvt
H7xsD821+iO2zt6bETOXpClMfZOfvUq8k+0DGuOPz+VtUFrWlymUWoCwSXrbLpX9
uMq/NzgtHj6RQa1wVsfwTz/oMp50ysiQVOnGXw94nZpAPA6sYapeFI+eh6FqUNzX
mk6vBbOmcZSccbNQYArHE504B4YCqOmoaSYYkKtMsE8jqzpPhNjfzp/haW+710LX
a0Tkx63ubUFfclpxCDezeWWkWaCUN/cALw3CknLa0Dhy2xSoRcRdKn23tNbE7qzN
E0S3ySvdQwAl+mG5aWpYIxG3pzOPVnVZ9c0p10a3CitlttNCbxWyuHv77+ldU9U0
WicCAwEAAaOB3DCB2TAdBgNVHQ4EFgQUrb2YejS0Jvf6xCZU7wO94CTLVBowCwYD
VR0PBAQDAgEGMA8GA1UdEwEB/wQFMAMBAf8wgZkGA1UdIwSBkTCBjoAUrb2YejS0
Jvf6xCZU7wO94CTLVBqhc6RxMG8xCzAJBgNVBAYTAlNFMRQwEgYDVQQKEwtBZGRU
cnVzdCBBQjEmMCQGA1UECxMdQWRkVHJ1c3QgRXh0ZXJuYWwgVFRQIE5ldHdvcmsx
IjAgBgNVBAMTGUFkZFRydXN0IEV4dGVybmFsIENBIFJvb3SCAQEwDQYJKoZIhvcN
AQEFBQADggEBALCb4IUlwtYj4g+WBpKdQZic2YR5gdkeWxQHIzZlj7DYd7usQWxH
YINRsPkyPef89iYTx4AWpb9a/IfPeHmJIZriTAcKhjW88t5RxNKWt9x+Tu5w/Rw5
6wwCURQtjr0W4MHfRnXnJK3s9EK0hZNwEGe6nQY1ShjTK3rMUUKhemPR5ruhxSvC
Nr4TDea9Y355e6cJDUCrat2PisP29owaQgVR1EX1n6diIWgVIEM8med8vSTYqZEX
c4g/VhsxOBi0cQ+azcgOno4uG+GMmIPLHzHxREzGBHNJdmAPx/i9F4BrLunMTA5a
mnkPIAou1Z5jJh5VkpTYghdae9C8x49OhgQ=
-----END CERTIFICATE-----
" > /etc/ssl/private/tla.msr-inria.inria.fr.chain

echo "
-----BEGIN CERTIFICATE-----
MIIEejCCA2KgAwIBAgIRAJ5Fn6sJoC/4wJPLYwSKAPYwDQYJKoZIhvcNAQEFBQAw
NjELMAkGA1UEBhMCTkwxDzANBgNVBAoTBlRFUkVOQTEWMBQGA1UEAxMNVEVSRU5B
IFNTTCBDQTAeFw0xNDA5MjIwMDAwMDBaFw0xNzA5MjEyMzU5NTlaMEQxITAfBgNV
BAsTGERvbWFpbiBDb250cm9sIFZhbGlkYXRlZDEfMB0GA1UEAxMWdGxhLm1zci1p
bnJpYS5pbnJpYS5mcjCCASIwDQYJKoZIhvcNAQEBBQADggEPADCCAQoCggEBAOPd
v577HMVgm/ZgMf/2RAkAqI1OZcmLDKCDfzujvu3ZdsC6WdcH1yKpW5DLibzsOJqR
TDLc64KCPMyBsnH+uQXCanQMhz1jKAvQS9duXP3BpChFFTC1ubAHmTxbBH7ip+Ju
rvubQEgdjaTp1q/St/d5IdxSssIF0RdZOYPrjYBWjPF1qq5ECS5uKQiiXAqVV5Zp
xczJ4/xjhHC+Uu1fgplrJMW/YnSCQbf8/VmFUNerZFOM6Zlt22gkIsGmGkYVnQ8B
OEyu6aagdcak8aontZq+hSiaID3g7AiTMF6jPV+OGI60D9+jlVbQKZHBi23/4G6Z
6JJbW9c6SInz+2ZGZlcCAwEAAaOCAXMwggFvMB8GA1UdIwQYMBaAFAy9k2gM896r
o0lrKzdXR+qQ47ntMB0GA1UdDgQWBBQcx9qzpuZmOH+ttUF1sNWCYsi3QTAOBgNV
HQ8BAf8EBAMCBaAwDAYDVR0TAQH/BAIwADAdBgNVHSUEFjAUBggrBgEFBQcDAQYI
KwYBBQUHAwIwIgYDVR0gBBswGTANBgsrBgEEAbIxAQICHTAIBgZngQwBAgEwOgYD
VR0fBDMwMTAvoC2gK4YpaHR0cDovL2NybC50Y3MudGVyZW5hLm9yZy9URVJFTkFT
U0xDQS5jcmwwbQYIKwYBBQUHAQEEYTBfMDUGCCsGAQUFBzAChilodHRwOi8vY3J0
LnRjcy50ZXJlbmEub3JnL1RFUkVOQVNTTENBLmNydDAmBggrBgEFBQcwAYYaaHR0
cDovL29jc3AudGNzLnRlcmVuYS5vcmcwIQYDVR0RBBowGIIWdGxhLm1zci1pbnJp
YS5pbnJpYS5mcjANBgkqhkiG9w0BAQUFAAOCAQEAiwiIvHeASa+SFniavhVFIayI
EmaRQKv35KIV2/MyTumroXSS7RntMOwC2ZeMfKc0P6/P6Lgz+gLTA9srS2sdEji2
0kctsZ5zqoAAN9Nrv55ry+7Mg7FJlvFcvz2fUqy0y7poToVv+Bni7abzgpUNgUYf
FUyWqKiTX9UZIKDa/1/xYxDiK2csXH2287+E6Zn/hZNlTj2Nx4donpbjTkASirjl
Ss/TeW2eKXldk93y80ZELwgUbzZqlHqqbWI39Z2JjyAxLhbJeeg8HpKY9Po9lrsL
pPp6GSqywJ9cehcpRDO7tJpK3xUUUOtsMX9SVat1a/RxiGBwvol7DxsrmKxK7g==
-----END CERTIFICATE-----
" > /etc/ssl/private/tla.msr-inria.inria.fr.crt

# Apache fails to start without the key file, thus touch
touch /etc/ssl/private/tla.msr-inria.inria.fr.key
echo "Manually copy the PRIVATE key to /etc/ssl/private/tla.msr-inria.inria.fr.key!!!"

## Restart Apache to pick up config changes (will fail due to missing SSL privkey)
service apache2 restart

##
## Create symlinks in /var/www pointing into /mnt/jenkins/jobs/...
##
ln -s /mnt/jenkins/jobs/M-HEAD-pdf4eclipse/lastSuccessful/archive/de.vonloesch.pdf4eclipse.p2repository/target/repository/ /var/www/html/pdf4eclipse
ln -s /mnt/jenkins/jobs/jmx2munin/lastSuccessful/archive/target /var/www/html/jmx2munin
ln -s /mnt/jenkins/jobs/apache-jclouds/lastStable/archive/target/repository/ /var/www/html/jclouds2p2

mkdir /var/www/html/tlatoolbox  
ln -s /mnt/jenkins/jobs/Release-HEAD-Toolbox.product.standalone/configurations/axis-os/master/lastPromoted/archive/tlatools/dist/ /var/www/html/tlatoolbox/dist
ln -s /mnt/jenkins/jobs/Release-HEAD-Toolbox.product.standalone/configurations/axis-os/master/lastPromoted/archive/org.lamport.tla.toolbox.doc/html /var/www/html/tlatoolbox/doc
ln -s /mnt/jenkins/jobs/Release-HEAD-Toolbox.product.standalone/configurations/axis-os/master/lastPromoted/archive/org.lamport.tla.toolbox.product.product/target/products /var/www/html/tlatoolbox/products
ln -s /mnt/jenkins/jobs/Release-HEAD-Toolbox.product.standalone/configurations/axis-os/master/lastPromoted/archive/org.lamport.tla.toolbox.product.product/target/repository /var/www/html/tlatoolbox/toolboxUpdate

mkdir /var/www/html/staged  
ln -s /mnt/jenkins/jobs/Release-HEAD-Toolbox.product.standalone/configurations/axis-os/master/lastStable/archive/tlatools/dist/ /var/www/html/tlatoolbox/staged/dist
ln -s /mnt/jenkins/jobs/Release-HEAD-Toolbox.product.standalone/configurations/axis-os/master/lastStable/archive/org.lamport.tla.toolbox.doc/html /var/www/html/tlatoolbox/staged/doc
ln -s /mnt/jenkins/jobs/Release-HEAD-Toolbox.product.standalone/configurations/axis-os/master/lastStable/archive/org.lamport.tla.toolbox.product.product/target/products /var/www/html/tlatoolbox/staged/products
ln -s /mnt/jenkins/jobs/Release-HEAD-Toolbox.product.standalone/configurations/axis-os/master/lastStable/archive/org.lamport.tla.toolbox.product.product/target/repository /var/www/html/tlatoolbox/staged/toolboxUpdate

mkdir /var/www/html/tlatoolbox/ci  
ln -s /mnt/jenkins/jobs/M-HEAD-Toolbox.product.standalone/configurations/axis-os/master/lastSuccessful/archive/tlatools/dist/ /var/www/html/tlatoolbox/ci/tladist
ln -s /mnt/jenkins/jobs/M-HEAD-Toolbox.product.standalone/configurations/axis-os/master/lastSuccessful/archive/org.lamport.tla.toolbox.doc/html /var/www/html/tlatoolbox/ci/doc
ln -s /mnt/jenkins/jobs/M-HEAD-Toolbox.product.standalone/configurations/axis-os/master/lastSuccessful/archive/org.lamport.tla.toolbox.product.product/target/products /var/www/html/tlatoolbox/ci/products
ln -s /mnt/jenkins/jobs/M-HEAD-Toolbox.product.standalone/configurations/axis-os/master/lastSuccessful/archive/org.lamport.tla.toolbox.product.product/target/repository /var/www/html/tlatoolbox/ci/toolboxUpdate

## Manually pull jenkins config in from private git repo (it's done manually to not store the private keys publically)
echo "1a) Add the private parts of the SSH and SSL keys (see output above)"
echo "1b) If the SSH key couldn't be restored, make sure the new key is added to bitbucket.org/lemmster/tla.msr-inria.inria.fr (read & write)."
echo "1c) Start apache2 webserver."

echo "2a) Go to Jenkin's management page and update its plugins to latest."
echo "2b) Stop Jenkins on the command line (/etc/init.d/jenkins stop)."

echo "3a) Clone 'git@bitbucket.org:lemmster/tla.msr-inria.inria.fr.git' to /tmp and copy its content to /mnt/jenkins/ (omitting .git directory)"
echo "3b) Recursively chown the copied files in /mnt/jenkins to jenkins:nogroup."

echo "4) As user jenkins launch vncserver once and set a random password."

echo "5) Start Jenkins and the old installation should be restored."


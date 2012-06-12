#!/bin/bash

# allow user mkuppe to use sudo without password
sed -i 's/%sudo ALL=(ALL) ALL/%sudo ALL=(ALL) NOPASSWD: ALL/g' /etc/sudoers
usermod -G sudo -a mkuppe

# update package index and install basic packages needed
export DEBIAN_FRONTEND=noninteractive
apt-get update
apt-get upgrade -y
apt-get --no-install-recommends install ant openjdk-6-jdk unzip mc htop sysstat apache2 munin munin-node munin-java-plugins munin-plugins-extra git git-svn sshfs rsync -y

# if UI/X needed
apt-get --no-install-recommends install gnome-core gdm iceweasel tightvncserver xorg -y

# clear cached packages to save disk space
apt-get clean

# add jar and script to munin
cp /home/mkuppe/grid5000.git/tools/jmx2munin/jmx2munin-1.0.jar /usr/share/munin/jmx2munin.jar
cp /home/mkuppe/grid5000.git/tools/jmx2munin/jmx2munin.sh /usr/share/munin/plugins
chmod +x /usr/share/munin/plugins/jmx2munin.sh
# try saving a few bytes
P1=/etc/munin/plugins
P2=/usr/share/munin/plugins
# activate extra munin stats
rm $P1/apache_*
rm $P1/munin_*
rm $P1/http_*
rm $P1/fw_*
# for jmx plugin to work, the vm has to be started with -D properties to listen on port 5400
ln -s $P2/jmx_ $P1/jmx_ClassesLoaded
ln -s $P2/jmx_ $P1/jmx_ClassesLoadedTotal
ln -s $P2/jmx_ $P1/jmx_ClassesUnloaded
ln -s $P2/jmx_ $P1/jmx_CompilationTimeTotal
ln -s $P2/jmx_ $P1/jmx_GCCount
ln -s $P2/jmx_ $P1/jmx_GCTime
ln -s $P2/jmx_ $P1/jmx_CurrentThreadCpuTime
ln -s $P2/jmx_ $P1/jmx_CurrentThreadUserTime
ln -s $P2/jmx_ $P1/jmx_MemoryAllocatedHeap
ln -s $P2/jmx_ $P1/jmx_MemoryAllocatedNonHeap
ln -s $P2/jmx_ $P1/jmx_MemoryEdenPeak
ln -s $P2/jmx_ $P1/jmx_MemoryEdenUsage
ln -s $P2/jmx_ $P1/jmx_MemoryEdenUsagePostGC
ln -s $P2/jmx_ $P1/jmx_MemoryObjectsPending
ln -s $P2/jmx_ $P1/jmx_MemoryPermGenPeak
ln -s $P2/jmx_ $P1/jmx_MemoryPermGenUsage
ln -s $P2/jmx_ $P1/jmx_MemoryPermGenUsagePostGC
ln -s $P2/jmx_ $P1/jmx_MemorySurvivorPeak
ln -s $P2/jmx_ $P1/jmx_MemorySurvivorUsage
ln -s $P2/jmx_ $P1/jmx_MemorySurvivorUsagePostGC
ln -s $P2/jmx_ $P1/jmx_MemoryTenuredGenPeak
ln -s $P2/jmx_ $P1/jmx_MemoryTenuredGenUsage
ln -s $P2/jmx_ $P1/jmx_MemoryTenuredGenUsagePostGC
ln -s $P2/jmx_ $P1/jmx_MemorythresholdPostGCCount
ln -s $P2/jmx_ $P1/jmx_MemorythresholdUsageCount
ln -s $P2/jmx_ $P1/jmx_ProcessorsAvailable
ln -s $P2/jmx_ $P1/jmx_Threads
ln -s $P2/jmx_ $P1/jmx_ThreadsDaemon
ln -s $P2/jmx_ $P1/jmx_ThreadsDeadlocked
ln -s $P2/jmx_ $P1/jmx_ThreadsPeak
ln -s $P2/jmx_ $P1/jmx_ThreadsStartedTotal
ln -s $P2/jmx_ $P1/jmx_Uptime
# activate DiskFPSet0 stats
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::filecnt
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::tblcnt
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::indexcnt
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::disklookupcnt
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::diskwritecnt
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::diskhitcnt
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::diskseekcnt
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::memhitcnt
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::growdiskmark
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::checkpointmark
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::bucketcapacity
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::tblcapacity
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::overallcapacity
# activate ModelChecker stats
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:ModelChecker::distinctstatesgenerated
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:ModelChecker::progress
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:ModelChecker::distinctstatesgeneratedperminute
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:ModelChecker::statequeuesize
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:ModelChecker::statesgenerated
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:ModelChecker::statesgeneratedperminute
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:ModelChecker::workercount
# Lock contention
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-0::waitedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-0::blockedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-1::waitedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-1::blockedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-2::waitedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-2::blockedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-3::waitedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-3::blockedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-4::waitedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-4::blockedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-5::waitedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-5::blockedtime

# Replace localhost.localdomain string in config file
sed -i 's/localhost.localdomain/tlc/g' /etc/munin/munin.conf

# restart munin after config changes
service munin-node restart

# allow everybody to see munin stats
echo "RedirectMatch ^/$ /munin
Alias /munin /var/cache/munin/www
<Directory /var/cache/munin/www>
        Order allow,deny
        Allow from all
        Options None
</Directory>
" > /etc/munin/apache.conf
service apache2 restart


#!/bin/bash

ROOT_DIR=`dirname $0`

# install custom build of munin-java-plugins cause it fixes a bug that prevents the upstream build from reporting GarbageCollectionTime
dpkg -i $ROOT_DIR/munin-java-plugins_1.4.6-3ubuntu3.1_all.deb

# add jar and script to munin
cp $ROOT_DIR/jmx2munin-1.0.jar /usr/share/munin/jmx2munin.jar
cp $ROOT_DIR/jmx2munin.sh /usr/share/munin/plugins
chmod +x /usr/share/munin/plugins/jmx2munin.sh
# try saving a few bytes
P1=/etc/munin/plugins
P2=/usr/share/munin/plugins
# activate extra munin stats
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
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::flushtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::tblload
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::diskseekcache
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::diskseekrate
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::collisionbucketcnt
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::collisionratio
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::loadfactor
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::maxtblcnt
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::readerwritercnt
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet0::sizeof
# activate DiskFPSet1 stats
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet1::filecnt
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet1::tblcnt
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet1::indexcnt
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet1::disklookupcnt
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet1::diskwritecnt
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet1::diskhitcnt
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet1::diskseekcnt
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet1::memhitcnt
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet1::growdiskmark
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet1::checkpointmark
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet1::bucketcapacity
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet1::tblcapacity
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet1::overallcapacity
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet1::flushtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet1::tblload
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet1::diskseekcache
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet1::diskseekrate
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet1::collisionbucketcnt
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet1::collisionratio
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet1::loadfactor
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet1::maxtblcnt
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet1::readerwritercnt
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:fp:DiskFPSet1::sizeof
# activate ModelChecker stats
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:ModelChecker::distinctstatesgenerated
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:ModelChecker::progress
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:ModelChecker::distinctstatesgeneratedperminute
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:ModelChecker::statequeuesize
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:ModelChecker::statesgenerated
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:ModelChecker::statesgeneratedperminute
ln -s $P2/jmx2munin.sh $P1/jmx2munin_tlc2:tool:ModelChecker::workercount
# Lock contention
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-000::waitedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-000::blockedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-001::waitedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-001::blockedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-002::waitedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-002::blockedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-003::waitedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-003::blockedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-004::waitedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-004::blockedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-005::waitedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-005::blockedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-006::waitedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-006::blockedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-007::waitedtime
ln -s $P2/jmx2munin.sh $P1/jmx2munin_org:vafer:jmx:contention:TLCWorkerThread-007::blockedtime

# Replace localhost.localdomain string in config file
sed -i 's/localhost.localdomain/tlc/g' /etc/munin/munin.conf

# remove unused system stats 
rm $P1/apache_*
rm $P1/munin_*
rm $P1/http_*
rm $P1/fw_*

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


#!/bin/bash
#
# Munin magic markers
#%# family=auto
#%# capabilities=autoconf
#

#set -x

# cut off the part after _ in symlink name
scriptname=${0##*/}
jmxfunc=${scriptname##*_}

# string manipulation (remove from front and back)
package_with_class=${jmxfunc%%::*}
package=${package_with_class%:*}
package_with_underscore=${package//:/_}
package_with_dots=${package//:/.}

# split of class name
class=${package_with_class##*:}
class_without_instance=${class%%-*}
class_lower=${class,,}
class_lower_without_instance=${class_lower%%-*}

instance=${class#*-}

if [ $class = $instance ]; then
	instance=
fi

# split of attribute part
attribute=${jmxfunc##*::}

# create query string
query=$package_with_dots':type='$class_without_instance

config='tlc2/tlc'

if [ -z "$MUNIN_LIBDIR" ]; then
    MUNIN_LIBDIR="`dirname $(dirname "$0")`"
fi

if [ -f "$MUNIN_LIBDIR/plugins/plugin.sh" ]; then
    . $MUNIN_LIBDIR/plugins/plugin.sh
fi

# we support munin autoconf
if [ "$1" = "autoconf" ]; then
    echo yes
    exit 0
fi

# this is very common so make it a default
if [ -z "$url" ]; then
  url="service:jmx:rmi:///jndi/rmi://127.0.0.1:5400/jmxrmi"
fi

if [ -z "$query" -o -z "$url" ]; then
  echo "Configuration needs attributes query and optinally url"
  exit 1
fi

JMX2MUNIN_DIR="/etc/munin/plugin-conf.d"

# if config as parameter request, munin wants to know how to layout this graph
if [ "$1" = "config" ]; then
                         echo graph_title $class $attribute
    echo graph_scale yes
    echo graph_category tlc
    echo graph_vlabel $attribute
    echo $package_with_underscore'_'$class_lower_without_instance$instance'_'$attribute.label $attribute
    exit 0
fi

JAR="/usr/share/munin/jmx2munin.jar"
CACHED="/tmp/jmx2munin_"$package_with_dots'.'$class_lower_without_instance

# refresh cached file if necessary
if test ! -f $CACHED || test `find "$CACHED" -mmin +2`; then

    #java -cp /usr/local/src/jmx2munin/target/classes:/usr/local/src/.m2/repository/com/beust/jcommander/1.17/jcommander-1.17.jar org.vafer.jmx.munin.Munin \
    java -jar "$JAR" \
      -url "$url" \
      -query "$query" \
      > $CACHED

    echo "cached.value `date +%s`" >> $CACHED
fi

# read fresh or cached value from cache file
ATTRIBUTE=$package_with_underscore'_'$class_lower_without_instance$instance'_'$attribute.value
grep $ATTRIBUTE $CACHED

exit 0

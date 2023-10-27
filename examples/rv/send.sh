#!/bin/bash -x

DEVICE=/dev/ttyUSB1
PROG=tests/_build/rv32i/integ/tiny.rv32

SEGINFO=$(readelf --segments $PROG | grep "Program Headers:" -A 2 | tail -n 1 | column -t)
SEGOFS=$(echo $SEGINFO | cut -f 2 -d ' ')
SEGSIZE=$(echo $SEGINFO | cut -f 5 -d ' ')

SEGOFS=$(printf "%d" $SEGOFS)
SEGSIZE=$(printf "%d" $SEGSIZE)


tail -c +$((SEGOFS+1)) $PROG | head -c $SEGSIZE > /tmp/prog

int2hex(){
    HEXSTR=`printf "%08x" $1`
    BYTE1=`echo -n "$HEXSTR" | cut -c 1-2`
    BYTE2=`echo -n "$HEXSTR" | cut -c 3-4`
    BYTE3=`echo -n "$HEXSTR" | cut -c 5-6`
    BYTE4=`echo -n "$HEXSTR" | cut -c 7-8`
    echo -ne "\x$BYTE1\x$BYTE2\x$BYTE3\x$BYTE4"
}

ENTRY=$(readelf -h $PROG| grep "Entry point" | cut -d ':' -f 2 | column -t)

int2hex $SEGSIZE | pv -L 20 > $DEVICE
int2hex $ENTRY | pv -L 20 > $DEVICE
cat /tmp/prog | pv -L 15 > $DEVICE

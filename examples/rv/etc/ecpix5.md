```
make \
    ECP5_TOP=top_ecpix5.v \
    ECP5_DEVICE=45k \
    ECP5_LPF=ecpix5.lpf \
    ECP5_PACKAGE=CABGA554 \
    top_ecpix5.bit

ecppack \
    --compress top_ecpix5.config \
    --idcode 0x81112043 top_ecpix5.bit

openFPGALoader -b ecpix5 top_ecpix5.bit
```

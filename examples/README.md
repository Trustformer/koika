# Examples
Useful `Makefile` targets in `_objects/<example_name>`:
`make obj_dir/V<name>` Compile the generated RTL with Verilator.
`make gdb` Compile the C++ model of your design in debug mode, then run it under GDB.
`make <name>.hpp.gcov` Generate coverage statistics for the C++ model of your design (this shows which rules firer, how often then fire, and why they fail when they do).
`make NCYCLES=25 gtkwave.verilator` Compile the generated RTL with Verilator in `--trace` mode, then a VCD trace over 25 cycles and open it in GTKWave.
The Makefiles that `cuttlec` generates include targets for generating ECP5 and ICE40 bitstreams.

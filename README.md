msp430
======

Emulator for the MSP430 for #uctf

This exists because the final level of the Matasano/Square CTF at microcorruption.com runs for too many steps to make stepping through to find the code that actually unlocks the door plausible.  This solves the problem by producing a log file listing every instruction executed in the level, which can then be searched for the ones that actually solve the problem.

To run, copy the starting memory state from the CTF web-app into a text file, and use run-level.

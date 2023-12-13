# argu

argu is verified tool for finding and checking the grounded extention of
an argumentation framework. The existence and uniqueness of the grounded
extension as well as the existence of preferred extensions have been
verified based on a trick for implementing higher-order quantification
in SPARK.

Currently, the input handling is not yet implemented properly, so the
input needs to be included into the program in the file src/maind.adb.

To build the executable, run
gnatmake -P argu.gpr
in a terminal.

To run the program, run
./obj/main
in a terminal.

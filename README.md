-------------Emergence of Natural Selection-------------

1) Clone the repository with option --recurse-submodule  (or after clone, do "git init submodule" and "git submodule update --remote")
2) Install the required Juce version somewhere (like a "Software" folder) with "git clone --branch=develop-local https://github.com/benkuper/JUCE"
3) In the Juce folder, go in extras/Projucer/Builds/[YourOS]Makefile, and type make, or "make -j 4" to save time
4) Open Projucer (in the build folder) and load EmergenceNS.jucer
5) In File>Global path, you can add the Path to Juce if necessary.
6) Choose your plateform (linux, mac, windows) in "selected exporter", and save the project.
7) You can try to go in "EmergenceNS/Builds/your system" and compile with "make -j 4"
8) make sure you have minisat installed and that the command "minisat" works.



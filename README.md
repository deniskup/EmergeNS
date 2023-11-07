-------------Emergence of Natural Selection-------------

1) ```git clone --recurse-submodule git@github.com:deniskup/EmergenceNS.git``` (or after clone, do "git init submodule" and "git submodule update --remote")
2) checkout  the working commit for juce_organicui : in the Modules/juce_organicui do ```git reset--hard 55c3fd79bf74d03bad7262318843ece9d608e76e```
3) Install the required Juce version somewhere (like a "Software" folder) with ```git clone --branch=develop-local https://github.com/benkuper/JUCE```
4) In the Juce folder, go in extras/Projucer/Builds/[YourOS]Makefile
   
   For Linux ```make -j 4```

   For Mac ```sudo xcodebuild -project Builds/MacOSX/MyApp.xcodeproj -alltargets -parallelizeTargets -configuration Release build```
5) Open Projucer (in the build folder) and load EmergenceNS.jucer
6) In File>Global path, you can add the Path to Juce if necessary.
7) Choose your plateform (linux, mac, windows) in "selected exporter", and save the project.
8) You can try to go in "EmergenceNS/Builds/your system" and use the ame command as in item 4
9) make sure you have z3 installed and that the command "z3" works.



-------------Emergence of Natural Selection-------------

1. ```git clone --recurse-submodule git@github.com:deniskup/EmergenceNS.git``` (or after clone, do "git init submodule" and "git submodule update --remote")

2. Install the required Juce version somewhere (like a "Software" folder) with <br>
 ```git clone --branch=develop-local https://github.com/benkuper/JUCE```

3. In the Juce folder, go in extras/Projucer/Builds/[YourOS] <br>
   For Linux ```make -j 4```<br>
   For Mac open with xcode and compile, or ```sudo xcodebuild -project Builds/MacOSX/EmergenceNS.xcodeproj -alltargets -parallelizeTargets -configuration Release build```<br>
4. Open Projucer (in the build folder) and load EmergenceNS.jucer<br>

5. In File>Global path, add the Path to Juce.

6. Save the project

7. You can go in "EmergenceNS/Builds/your system" and use the same command as in item 4

8. Make sure you have z3 installed and that the command "z3" works in your terminal.



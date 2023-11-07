-------------Emergence of Natural Selection-------------

1. ```git clone --recurse-submodule git@github.com:deniskup/EmergenceNS.git``` (or after clone, do "git init submodule" and "git submodule update --remote")
2. checkout  the working commit for juce_organicui : in the Modules/juce_organicui do <br>
```git reset--hard 55c3fd79bf74d03bad7262318843ece9d608e76e```

3. Install the required Juce version somewhere (like a "Software" folder) with <br>
 ```git clone --branch=develop-local https://github.com/benkuper/JUCE```

4. In the Juce folder, go in extras/Projucer/Builds/[YourOS]Makefile <br>
   For Linux ```make -j 4```<br>
   For Mac ```sudo xcodebuild -project Builds/MacOSX/EmergenceNS.xcodeproj -alltargets -parallelizeTargets -configuration Release build```<br>
5. Open Projucer (in the build folder) and load EmergenceNS.jucer<br>

6. In File>Global path, add the Path to Juce.

7. Save the project

8. You can go in "EmergenceNS/Builds/your system" and use the same command as in item 4

9. Make sure you have z3 installed and that the command "z3" works in your terminal.



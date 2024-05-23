-------------Emergence of Natural Selection-------------

1. ```git clone --recurse-submodule https://github.com/deniskup/EmergenceNS.git``` (or after clone, do "git init submodule " and "git submodule update --init --recursive")

2. Install the required Juce version somewhere (like a "Software" folder) with <br>
 ```git clone --branch=develop-local https://github.com/benkuper/JUCE```

3. In the Juce folder, go in extras/Projucer/Builds/[YourOS] <br>
   For Linux ```make -j 4```<br>
   For Mac open  Projucer.xcodeproj with xcode and compile<br>
   
4. Open Projucer (in the build folder) and load EmergenceNS.jucer<br>

5. In File>Global path, add the Path to Juce. For Windows add "/bigobj" in "Extra Compiler Flags" of Exporters>Visual Studio Code if it's not there already.

6. Save the project

7. Make sure you have z3 installed and that the command "z3" works in your terminal.

8. Make sure you have msolve installed and the command "msolve" works in your terminal.
If not, check the webpage https://msolve.lip6.fr to install it. Installation procedure is explained on the INSTALL file of the associated github page (see 'github' thread on the msolve web page).
You will need to have GMP and FLINT libraries installed on your system. For ubuntu users, you can type :
   ```sudo apt get libgmp-dev```
   ```sudo apt get libflint-dev```


=> Next steps to be done after every git pull:

9. Compile with xcode '.../EmergenceNS/Builds/MacOSX/EmergenceNS.xcodeproj'
/!\ Warning: on mac use version 14 or less

10. In case z3 is not found, specify path (e.g. /usr/local/bin/z3) in View/Settings

11. In case solve is not found, specify path (e.g. /usr/local/bin/z3) in View/Settings




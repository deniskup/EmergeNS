![Screenshot](bifurc.png)

-------------Emergence of Natural Selection-------------

1. ```git clone --recurse-submodule https://github.com/deniskup/EmergeNS.git``` (or after clone, do "git init submodule " and "git submodule update --init --recursive")

2. Install the required Juce version somewhere (like a "Software" folder) with <br>
 ```git clone --branch=develop-local https://github.com/benkuper/JUCE```

3. In the Juce folder, go in extras/Projucer/Builds/[YourOS] <br>
   For Linux :<br>
    - install all necessary dependencies: ```sudo apt install g++ libfreetype6-dev libcurl4-openssl-dev libx11-dev libxrand-dev libxinerama-dev libxcursos-dev```<br>
    - compile with ```make -j 4```<br>
    
   For Mac open  Projucer.xcodeproj with xcode and compile<br>


 
   
5. Open Projucer (in the build folder) and load EmergeNS.jucer<br>

6. Clic on the icon on the top right to sign in, and then "Enable GPL mode"<br>

7. In File>Global path, add the Path to Juce.For Windows add "/bigobj" in "Extra Compiler Flags" of Exporters>Visual Studio Code if it's not there already.<br>

8. Save the project<br>

9. Make sure you have z3 installed and that the command "z3" works in your terminal (you can also specify a path to the exectuable in the software settings).<br>

10. For multistability detection (optional): Make sure you have msolve installed and the command "msolve" works in your terminal.
If not, check the webpage https://msolve.lip6.fr to install it. Installation procedure is explained on the INSTALL file of the associated github page (see 'github' thread on the msolve web page).
You will need to have GMP and FLINT libraries installed on your system. For ubuntu users, you can type :
   ```sudo apt get libgmp-dev```
   ```sudo apt get libflint-dev```


=> Next steps to be done after every git pull:

11. Compile with xcode '.../EmergeNS/Builds/MacOSX/EmergeNS.xcodeproj' for Mac, or with ```make -j 2``` in EmergeNS/Builds/LinuxMakefile for Linux
    
/!\ Warning: on Mac use version 14 or less of xcode

Possible errors and how to fix

   - ft2build.h missing  ->  in Projucer, add "/usr/include/freetype2" in the Header Search Paths of "Debug" and "Release" config of Linux MakeFile
   - package gtk+ not found -> ```sudo apt install build-essential libgtk-3-dev```
   - package webkit2gtk-4.0 not found -> ```sudo apt install libwebkit2gtk-4.0-dev```
     
12. On Mac, the compiled program must be launched with sudo so that it can access external programs such as z3. The compiled program is in your EmergeNS folder, then (in debug mode for instance) ``` sudo Builds/MacOSX/build/Debug/EmergeNS.app/Contents/MacOS/EmergeNS```

13. In case z3 is not found, specify path (e.g. /usr/local/bin/z3) in View/Settings




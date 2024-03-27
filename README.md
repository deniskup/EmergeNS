-------------Emergence of Natural Selection-------------

1. ```git clone --recurse-submodule https://github.com/deniskup/EmergenceNS.git``` (or after clone, do "git init submodule " and "git submodule update --init --recursive")

2. Install the required Juce version somewhere (like a "Software" folder) with <br>
 ```git clone --branch=develop-local https://github.com/benkuper/JUCE```

3. In the Juce folder, go in extras/Projucer/Builds/[YourOS] <br>
   For Linux ```make -j 4```<br>
   For Mac open  Projucer.xcodeproj with xcode and compile<br>

Possible errors and how to fix

   - Compiler g++ must be installed:  ```sudo apt install g++```
   - If you get an error about package freetype2 missing, install package libfreetype6-dev with ```sudo apt install libfreetype6-dev```
   - If you get an error about file curl.h missing, install virtual package libcurl-dev with e.g. ```sudo apt install libcurl4-openssl-dev```
   - Xlib.h missing  ->  ```sudo apt install libx11-dev```
   - Xrandr.h missing  ->  ```sudo apt install libxrandr-dev```
   - Xinerama.h missing  ->  ```sudo apt install libxinerama-dev```
   - Xcursor.h missing  ->  ```sudo apt install libxcursor-dev```
 
   
5. Open Projucer (in the build folder) and load EmergenceNS.jucer<br>

6. In File>Global path, add the Path to Juce.

7. Click on the top right icon: "Sign in", and select "Enable GPL Mode"

8. Save the project in File->Save Project

9. Make sure you have z3 installed (```sudo apt install z3```) and that the command "z3" works in your terminal.

=> Next steps to be done after every git pull:

8. Compile with xcode '.../EmergenceNS/Builds/MacOSX/EmergenceNS.xcodeproj' for Mac, or with ```make -j 2``` in EmergenceNS/Builds/LinuxMakefile for Linux
/!\ Warning: on Mac use version 14 or less

Possible errors and how to fix

   - ft2build.h missing  ->  in Projucer, add "/usr/include/freetype2" in the Header Search Paths of "Debug" and "Release" config of Linux MakeFile
   - package gtk+ not found -> ```sudo apt install build-essential libgtk-3-dev```
   - package webkit2gtk-4.0 not found -> ```sudo apt install libwebkit2gtk-4.0-dev```
     
10. In case z3 is not found, specify path (e.g. /usr/local/bin/z3) in View/Settings




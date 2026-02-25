![Screenshot](bifurc.png)

-------------Emergence of Natural Selection-------------

-----to run the executable-----

Download [the latest release](https://github.com/deniskup/EmergeNS/releases/latest) and run it.<br>

On Linux: you will need fuse3: ```sudo apt install fuse3```<br>
On Mac: you need to grant access: after trying to launch, go to settings->security, and authorize the application.<br>

You can also use the predefined reaction systems from ReactionSystems.zip as examples.

-----to compile yourself-----

1. ```git clone --recurse-submodule https://github.com/deniskup/EmergeNS.git``` (or after clone, do "git init submodule " and "git submodule update --init --recursive")

2. Install the required Juce version somewhere (like a "Software" folder) with <br>
 ```git clone --branch=develop-local https://github.com/benkuper/JUCE```

3. In the Juce folder, go in extras/Projucer/Builds/[YourOS] <br>
   For Linux :<br>
    - install all necessary dependencies: ```sudo apt install g++ pkg-config libfreetype6-dev libcurl4-openssl-dev libx11-dev libxrand-dev libxinerama-dev libxcursos-dev```<br>
    - compile with ```make -j 4```<br>
    
   For Mac open  Projucer.xcodeproj with xcode and compile<br>

   For Windows, you need e.g. Visual Studio. Install the Component MSVC v143 v14.44-17.14 from "Individual Components", not the default one.
   Then use Visual Studio to open Projucer.sln, and build it with ctrl+shift+B
 
   
5. Open Projucer (in the build folder, in Windows it can be x64/Debug/App) and load EmergeNS.jucer<br>

6. Clic on the icon on the top right to sign in, and then "Enable GPL mode"<br>

7. In File>Global path, add the Path to Juce.For Windows add "/bigobj" in "Extra Compiler Flags" of Exporters>Visual Studio Code if it's not there already.<br>

Make sure to have the gsl library installed on your system, and that the paths indicated in the projucer files are correct. Go to "Linux Makefile", "Xcode (macOS)" or Visual Studio 2022 depending on your OS, and add the header and library paths respectively into "Header Search Paths" and "Extra Library Search Paths" windows, both for the debug and release options.
If you have a package manager, you should be able to install the gsl library "libgsl-dev" (linux), and for macOS using homebrew you could use "brew install gsl". For windows users, the gsl package should be found using MSYS2 or Cygwin.

8. Save the project<br>

9. Make sure you have z3 installed and that the command "z3" works in your terminal (you can also specify a path to the exectuable in the software settings).<br>

10. For multistability detection (optional): Make sure you have msolve installed and the command "msolve" works in your terminal.
If not, check the webpage https://msolve.lip6.fr to install it. Installation procedure is explained on the INSTALL file of the associated github page (see 'github' thread on the msolve web page).
You will need to have GMP and FLINT libraries installed on your system. For ubuntu users, you can type :
   ```sudo apt get libgmp-dev```
   ```sudo apt get libflint-dev```


=> Next steps to be done after every git pull:

11. For Linux:  ``make -j 2``` in EmergeNS/Builds/LinuxMakefile <br>
    For Mac: Compile with xcode '.../EmergeNS/Builds/MacOSX/EmergeNS.xcodeproj' 
    For Windows: ".../EmergeNS/Builds/VisualStudio2022/"
    
/!\ Warning: on Mac use version 14 or less of xcode

For dependencies: ```sudo apt install build-essential libgtk-4-dev ibwebkit2gtk-4.0-dev```

   - ft2build.h missing  ->  in Projucer, add "/usr/include/freetype2" in the Header Search Paths of "Debug" and "Release" config of Linux MakeFile
   - same with other libraries installed but not found, e.g. gtk/gtk.h, add your path to gtk/gtk.h in Projucer, for instance "/usr/include/gtk-4.0"
   - if you are on a too recent linux version and mibwebkit2gtk-4.0-dev is not available, download the 4.1and add a symbolic link to mimic the 4.0 version with ```cd /usr/lib/x86_64-linux-gnu/pkgconfig; sudo ln -s webkit2gtk-4.1.pc webkit2gtk-4.0.pc```
     
12. On Mac, the compiled program must be launched with sudo so that it can access external programs such as z3. The compiled program is in your EmergeNS folder, then (in debug mode for instance) ``` sudo Builds/MacOSX/build/Debug/EmergeNS.app/Contents/MacOS/EmergeNS```

13. In case z3 is not found, specify path (e.g. /usr/local/bin/z3) in View/Settings




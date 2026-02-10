# Automatically generated makefile, created by the Projucer
# Don't edit this file! Your changes will be overwritten when you re-save the Projucer project!

# build with "V=1" for verbose builds
ifeq ($(V), 1)
V_AT =
else
V_AT = @
endif

# (this disables dependency generation if multiple architectures are set)
DEPFLAGS := $(if $(word 2, $(TARGET_ARCH)), , -MMD)

ifndef PKG_CONFIG
  PKG_CONFIG=pkg-config
endif

ifndef STRIP
  STRIP=strip
endif

ifndef AR
  AR=ar
endif

ifndef CONFIG
  CONFIG=Debug
endif

JUCE_ARCH_LABEL := $(shell uname -m)

ifeq ($(CONFIG),Debug)
  JUCE_BINDIR := build
  JUCE_LIBDIR := build
  JUCE_OBJDIR := build/intermediate/Debug
  JUCE_OUTDIR := build

  ifeq ($(TARGET_ARCH),)
    TARGET_ARCH := 
  endif

  JUCE_CPPFLAGS := $(DEPFLAGS) "-DLINUX=1" "-DDEBUG=1" "-D_DEBUG=1" "-DJUCE_DISPLAY_SPLASH_SCREEN=0" "-DJUCE_USE_DARK_SPLASH_SCREEN=1" "-DJUCE_PROJUCER_VERSION=0x7000c" "-DJUCE_MODULE_AVAILABLE_juce_core=1" "-DJUCE_MODULE_AVAILABLE_juce_cryptography=1" "-DJUCE_MODULE_AVAILABLE_juce_data_structures=1" "-DJUCE_MODULE_AVAILABLE_juce_events=1" "-DJUCE_MODULE_AVAILABLE_juce_graphics=1" "-DJUCE_MODULE_AVAILABLE_juce_gui_basics=1" "-DJUCE_MODULE_AVAILABLE_juce_gui_extra=1" "-DJUCE_MODULE_AVAILABLE_juce_opengl=1" "-DJUCE_MODULE_AVAILABLE_juce_organicui=1" "-DJUCE_MODULE_AVAILABLE_juce_osc=1" "-DJUCE_GLOBAL_MODULE_SETTINGS_INCLUDED=1" "-DJUCE_STRICT_REFCOUNTEDPOINTER=1" "-DORGANICUI_USE_DASHBOARDPANEL=0" "-DORGANICUI_USE_PARROTPANEL=0" "-DORGANICUI_USE_DETECTIVEPANEL=0" "-DORGANICUI_USE_HELPPANEL=0" "-DJUCE_STANDALONE_APPLICATION=1" "-DWMULTICHAR=0" "-DJUCER_LINUX_MAKE_890A77D1=1" "-DJUCE_APP_VERSION=1.0.1" "-DJUCE_APP_VERSION_HEX=0x10001" $(shell $(PKG_CONFIG) --cflags freetype2 gl libcurl webkit2gtk-4.0 gtk+-x11-3.0) -pthread -I../../JuceLibraryCode -I../../JUCE/modules -I../../Modules -I../../Source -I../../External/Eigen/include $(CPPFLAGS)
  JUCE_CPPFLAGS_APP :=  "-DJucePlugin_Build_VST=0" "-DJucePlugin_Build_VST3=0" "-DJucePlugin_Build_AU=0" "-DJucePlugin_Build_AUv3=0" "-DJucePlugin_Build_AAX=0" "-DJucePlugin_Build_Standalone=0" "-DJucePlugin_Build_Unity=0" "-DJucePlugin_Build_LV2=0"
  JUCE_TARGET_APP := EmergeNS

  JUCE_CFLAGS += $(JUCE_CPPFLAGS) $(TARGET_ARCH) -g -ggdb -O0 $(CFLAGS)
  JUCE_CXXFLAGS += $(JUCE_CFLAGS) -std=c++17 $(CXXFLAGS)
  JUCE_LDFLAGS += $(TARGET_ARCH) -L$(JUCE_BINDIR) -L$(JUCE_LIBDIR) $(shell $(PKG_CONFIG) --libs freetype2 gl libcurl) -fvisibility=hidden -lrt -ldl -lpthread $(LDFLAGS)

  CLEANCMD = rm -rf $(JUCE_OUTDIR)/$(JUCE_TARGET_APP) $(JUCE_OBJDIR)
endif

ifeq ($(CONFIG),Release)
  JUCE_BINDIR := build
  JUCE_LIBDIR := build
  JUCE_OBJDIR := build/intermediate/Release
  JUCE_OUTDIR := build

  ifeq ($(TARGET_ARCH),)
    TARGET_ARCH := 
  endif

  JUCE_CPPFLAGS := $(DEPFLAGS) "-DLINUX=1" "-DNDEBUG=1" "-DJUCE_DISPLAY_SPLASH_SCREEN=0" "-DJUCE_USE_DARK_SPLASH_SCREEN=1" "-DJUCE_PROJUCER_VERSION=0x7000c" "-DJUCE_MODULE_AVAILABLE_juce_core=1" "-DJUCE_MODULE_AVAILABLE_juce_cryptography=1" "-DJUCE_MODULE_AVAILABLE_juce_data_structures=1" "-DJUCE_MODULE_AVAILABLE_juce_events=1" "-DJUCE_MODULE_AVAILABLE_juce_graphics=1" "-DJUCE_MODULE_AVAILABLE_juce_gui_basics=1" "-DJUCE_MODULE_AVAILABLE_juce_gui_extra=1" "-DJUCE_MODULE_AVAILABLE_juce_opengl=1" "-DJUCE_MODULE_AVAILABLE_juce_organicui=1" "-DJUCE_MODULE_AVAILABLE_juce_osc=1" "-DJUCE_GLOBAL_MODULE_SETTINGS_INCLUDED=1" "-DJUCE_STRICT_REFCOUNTEDPOINTER=1" "-DORGANICUI_USE_DASHBOARDPANEL=0" "-DORGANICUI_USE_PARROTPANEL=0" "-DORGANICUI_USE_DETECTIVEPANEL=0" "-DORGANICUI_USE_HELPPANEL=0" "-DJUCE_STANDALONE_APPLICATION=1" "-DWMULTICHAR=0" "-DJUCER_LINUX_MAKE_890A77D1=1" "-DJUCE_APP_VERSION=1.0.1" "-DJUCE_APP_VERSION_HEX=0x10001" $(shell $(PKG_CONFIG) --cflags freetype2 gl libcurl webkit2gtk-4.0 gtk+-x11-3.0) -pthread -I../../JuceLibraryCode -I../../JUCE/modules -I../../Modules -I../../Source -I../../External/Eigen/include $(CPPFLAGS)
  JUCE_CPPFLAGS_APP :=  "-DJucePlugin_Build_VST=0" "-DJucePlugin_Build_VST3=0" "-DJucePlugin_Build_AU=0" "-DJucePlugin_Build_AUv3=0" "-DJucePlugin_Build_AAX=0" "-DJucePlugin_Build_Standalone=0" "-DJucePlugin_Build_Unity=0" "-DJucePlugin_Build_LV2=0"
  JUCE_TARGET_APP := EmergeNS

  JUCE_CFLAGS += $(JUCE_CPPFLAGS) $(TARGET_ARCH) -O3 $(CFLAGS)
  JUCE_CXXFLAGS += $(JUCE_CFLAGS) -std=c++17 $(CXXFLAGS)
  JUCE_LDFLAGS += $(TARGET_ARCH) -L$(JUCE_BINDIR) -L$(JUCE_LIBDIR) $(shell $(PKG_CONFIG) --libs freetype2 gl libcurl) -fvisibility=hidden -lrt -ldl -lpthread $(LDFLAGS)

  CLEANCMD = rm -rf $(JUCE_OUTDIR)/$(JUCE_TARGET_APP) $(JUCE_OBJDIR)
endif

OBJECTS_APP := \
  $(JUCE_OBJDIR)/FirstExitTimeWorker_711a0755.o \
  $(JUCE_OBJDIR)/FirstExitTime_4857037.o \
  $(JUCE_OBJDIR)/EmergeNSEngine_29b22fc8.o \
  $(JUCE_OBJDIR)/KineticLaw_9fe9ae12.o \
  $(JUCE_OBJDIR)/EntityManagerUI_b4e33bac.o \
  $(JUCE_OBJDIR)/EntityUI_e6628173.o \
  $(JUCE_OBJDIR)/GenerationUI_294a2f68.o \
  $(JUCE_OBJDIR)/PACUI_82dd5f34.o \
  $(JUCE_OBJDIR)/PhasePlaneUI_e846d131.o \
  $(JUCE_OBJDIR)/ReactionManagerUI_528924e6.o \
  $(JUCE_OBJDIR)/ReactionUI_cc32579.o \
  $(JUCE_OBJDIR)/SettingsUI_93a423f3.o \
  $(JUCE_OBJDIR)/SimulationUI_fbb6fd17.o \
  $(JUCE_OBJDIR)/SpaceUI_f1b0aa68.o \
  $(JUCE_OBJDIR)/SimReaction_27eac781.o \
  $(JUCE_OBJDIR)/SimEntity_1d29d0fb.o \
  $(JUCE_OBJDIR)/PAC_277c22f3.o \
  $(JUCE_OBJDIR)/ReactionManager_91aee8a5.o \
  $(JUCE_OBJDIR)/Reaction_93dd6f32.o \
  $(JUCE_OBJDIR)/Entity_a854b0ec.o \
  $(JUCE_OBJDIR)/Generation_cf1dc9a1.o \
  $(JUCE_OBJDIR)/EntityManager_7f5721ab.o \
  $(JUCE_OBJDIR)/PhasePlane_233a49aa.o \
  $(JUCE_OBJDIR)/Settings_19ffc42c.o \
  $(JUCE_OBJDIR)/Simulation_ac703710.o \
  $(JUCE_OBJDIR)/SteadyStates_3910a3d.o \
  $(JUCE_OBJDIR)/Statistics_7698d42c.o \
  $(JUCE_OBJDIR)/Space_958d9267.o \
  $(JUCE_OBJDIR)/Util_9d757a8b.o \
  $(JUCE_OBJDIR)/Main_90ebc5c2.o \
  $(JUCE_OBJDIR)/MainComponent_a6ffb4a5.o \
  $(JUCE_OBJDIR)/MainComponentCommands_b1179f4d.o \
  $(JUCE_OBJDIR)/BinaryData_ce4232d4.o \
  $(JUCE_OBJDIR)/include_juce_core_f26d17db.o \
  $(JUCE_OBJDIR)/include_juce_cryptography_8cb807a8.o \
  $(JUCE_OBJDIR)/include_juce_data_structures_7471b1e3.o \
  $(JUCE_OBJDIR)/include_juce_events_fd7d695.o \
  $(JUCE_OBJDIR)/include_juce_graphics_f817e147.o \
  $(JUCE_OBJDIR)/include_juce_gui_basics_e3f79785.o \
  $(JUCE_OBJDIR)/include_juce_gui_extra_6dee1c1a.o \
  $(JUCE_OBJDIR)/include_juce_opengl_a8a032b.o \
  $(JUCE_OBJDIR)/include_juce_organicui_2c36794d.o \
  $(JUCE_OBJDIR)/include_juce_organicui2_5ab8c64f.o \
  $(JUCE_OBJDIR)/include_juce_organicui2b_ff2481bd.o \
  $(JUCE_OBJDIR)/include_juce_organicui3_5ac6ddd0.o \
  $(JUCE_OBJDIR)/include_juce_organicui4_5ad4f551.o \
  $(JUCE_OBJDIR)/include_juce_osc_f3df604d.o \

.PHONY: clean all strip

all : $(JUCE_OUTDIR)/$(JUCE_TARGET_APP)

$(JUCE_OUTDIR)/$(JUCE_TARGET_APP) : $(OBJECTS_APP) $(JUCE_OBJDIR)/execinfo.cmd $(RESOURCES)
	@command -v $(PKG_CONFIG) >/dev/null 2>&1 || { echo >&2 "pkg-config not installed. Please, install it."; exit 1; }
	@$(PKG_CONFIG) --print-errors freetype2 gl libcurl
	@echo Linking "EmergeNS - App"
	-$(V_AT)mkdir -p $(JUCE_BINDIR)
	-$(V_AT)mkdir -p $(JUCE_LIBDIR)
	-$(V_AT)mkdir -p $(JUCE_OUTDIR)
	$(V_AT)$(CXX) -o $(JUCE_OUTDIR)/$(JUCE_TARGET_APP) $(OBJECTS_APP) $(JUCE_LDFLAGS) $(shell cat $(JUCE_OBJDIR)/execinfo.cmd) $(JUCE_LDFLAGS_APP) $(RESOURCES) $(TARGET_ARCH)

$(JUCE_OBJDIR)/FirstExitTimeWorker_711a0755.o: ../../Source/Engine/FirstExitTimeWorker.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling FirstExitTimeWorker.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/FirstExitTime_4857037.o: ../../Source/Engine/FirstExitTime.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling FirstExitTime.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/EmergeNSEngine_29b22fc8.o: ../../Source/Engine/EmergeNSEngine.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling EmergeNSEngine.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/KineticLaw_9fe9ae12.o: ../../Source/Simulation/KineticLaw.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling KineticLaw.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/EntityManagerUI_b4e33bac.o: ../../Source/Simulation/ui/EntityManagerUI.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling EntityManagerUI.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/EntityUI_e6628173.o: ../../Source/Simulation/ui/EntityUI.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling EntityUI.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/GenerationUI_294a2f68.o: ../../Source/Simulation/ui/GenerationUI.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling GenerationUI.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/PACUI_82dd5f34.o: ../../Source/Simulation/ui/PACUI.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling PACUI.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/PhasePlaneUI_e846d131.o: ../../Source/Simulation/ui/PhasePlaneUI.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling PhasePlaneUI.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/ReactionManagerUI_528924e6.o: ../../Source/Simulation/ui/ReactionManagerUI.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling ReactionManagerUI.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/ReactionUI_cc32579.o: ../../Source/Simulation/ui/ReactionUI.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling ReactionUI.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/SettingsUI_93a423f3.o: ../../Source/Simulation/ui/SettingsUI.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling SettingsUI.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/SimulationUI_fbb6fd17.o: ../../Source/Simulation/ui/SimulationUI.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling SimulationUI.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/SpaceUI_f1b0aa68.o: ../../Source/Simulation/ui/SpaceUI.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling SpaceUI.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/SimReaction_27eac781.o: ../../Source/Simulation/SimReaction.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling SimReaction.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/SimEntity_1d29d0fb.o: ../../Source/Simulation/SimEntity.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling SimEntity.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/PAC_277c22f3.o: ../../Source/Simulation/PAC.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling PAC.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/ReactionManager_91aee8a5.o: ../../Source/Simulation/ReactionManager.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling ReactionManager.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/Reaction_93dd6f32.o: ../../Source/Simulation/Reaction.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling Reaction.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/Entity_a854b0ec.o: ../../Source/Simulation/Entity.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling Entity.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/Generation_cf1dc9a1.o: ../../Source/Simulation/Generation.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling Generation.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/EntityManager_7f5721ab.o: ../../Source/Simulation/EntityManager.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling EntityManager.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/PhasePlane_233a49aa.o: ../../Source/Simulation/PhasePlane.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling PhasePlane.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/Settings_19ffc42c.o: ../../Source/Simulation/Settings.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling Settings.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/Simulation_ac703710.o: ../../Source/Simulation/Simulation.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling Simulation.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/SteadyStates_3910a3d.o: ../../Source/Simulation/SteadyStates.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling SteadyStates.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/Statistics_7698d42c.o: ../../Source/Simulation/Statistics.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling Statistics.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/Space_958d9267.o: ../../Source/Simulation/Space.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling Space.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/Util_9d757a8b.o: ../../Source/Simulation/Util.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling Util.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/Main_90ebc5c2.o: ../../Source/Main.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling Main.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/MainComponent_a6ffb4a5.o: ../../Source/MainComponent.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling MainComponent.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/MainComponentCommands_b1179f4d.o: ../../Source/MainComponentCommands.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling MainComponentCommands.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/BinaryData_ce4232d4.o: ../../JuceLibraryCode/BinaryData.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling BinaryData.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/include_juce_core_f26d17db.o: ../../JuceLibraryCode/include_juce_core.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling include_juce_core.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/include_juce_cryptography_8cb807a8.o: ../../JuceLibraryCode/include_juce_cryptography.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling include_juce_cryptography.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/include_juce_data_structures_7471b1e3.o: ../../JuceLibraryCode/include_juce_data_structures.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling include_juce_data_structures.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/include_juce_events_fd7d695.o: ../../JuceLibraryCode/include_juce_events.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling include_juce_events.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/include_juce_graphics_f817e147.o: ../../JuceLibraryCode/include_juce_graphics.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling include_juce_graphics.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/include_juce_gui_basics_e3f79785.o: ../../JuceLibraryCode/include_juce_gui_basics.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling include_juce_gui_basics.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/include_juce_gui_extra_6dee1c1a.o: ../../JuceLibraryCode/include_juce_gui_extra.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling include_juce_gui_extra.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/include_juce_opengl_a8a032b.o: ../../JuceLibraryCode/include_juce_opengl.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling include_juce_opengl.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/include_juce_organicui_2c36794d.o: ../../JuceLibraryCode/include_juce_organicui.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling include_juce_organicui.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/include_juce_organicui2_5ab8c64f.o: ../../JuceLibraryCode/include_juce_organicui2.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling include_juce_organicui2.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/include_juce_organicui2b_ff2481bd.o: ../../JuceLibraryCode/include_juce_organicui2b.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling include_juce_organicui2b.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/include_juce_organicui3_5ac6ddd0.o: ../../JuceLibraryCode/include_juce_organicui3.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling include_juce_organicui3.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/include_juce_organicui4_5ad4f551.o: ../../JuceLibraryCode/include_juce_organicui4.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling include_juce_organicui4.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/include_juce_osc_f3df604d.o: ../../JuceLibraryCode/include_juce_osc.cpp
	-$(V_AT)mkdir -p $(@D)
	@echo "Compiling include_juce_osc.cpp"
	$(V_AT)$(CXX) $(JUCE_CXXFLAGS) $(JUCE_CPPFLAGS_APP) $(JUCE_CFLAGS_APP) -o "$@" -c "$<"

$(JUCE_OBJDIR)/execinfo.cmd:
	-$(V_AT)mkdir -p $(@D)
	-@if [ -z "$(V_AT)" ]; then echo "Checking if we need to link libexecinfo"; fi
	$(V_AT)printf "int main() { return 0; }" | $(CXX) -x c++ -o $(@D)/execinfo.x -lexecinfo - >/dev/null 2>&1 && printf -- "-lexecinfo" > "$@" || touch "$@"

$(JUCE_OBJDIR)/cxxfs.cmd:
	-$(V_AT)mkdir -p $(@D)
	-@if [ -z "$(V_AT)" ]; then echo "Checking if we need to link stdc++fs"; fi
	$(V_AT)printf "int main() { return 0; }" | $(CXX) -x c++ -o $(@D)/cxxfs.x -lstdc++fs - >/dev/null 2>&1 && printf -- "-lstdc++fs" > "$@" || touch "$@"

clean:
	@echo Cleaning EmergeNS
	$(V_AT)$(CLEANCMD)

strip:
	@echo Stripping EmergeNS
	-$(V_AT)$(STRIP) --strip-unneeded $(JUCE_OUTDIR)/$(JUCE_TARGET_APP)

-include $(OBJECTS_APP:%.o=%.d)

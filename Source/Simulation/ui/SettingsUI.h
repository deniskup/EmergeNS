
#pragma once

#include "../Settings.h"

class SettingsUI : public ShapeShifterContentComponent
            //public Settings::SettingsListener
{
public:
    SettingsUI();
    ~SettingsUI();

    Settings *settings;
    
    std::unique_ptr<GenericControllableContainerEditor> editorUI;

    void resized() override;

    static SettingsUI *create(const String &name) { return new SettingsUI(); }

    //void updateSettingsUI(Settings *) override;

};
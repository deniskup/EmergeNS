/* ==================================== JUCER_BINARY_RESOURCE ====================================

   This is an auto-generated file: Any edits you make may be overwritten!

*/

#include <cstring>

namespace BinaryData
{

//================== default.nslayout ==================
static const unsigned char temp_binary_data_0[] =
"{\n"
"  \"mainLayout\": {\n"
"    \"type\": 1,\n"
"    \"width\": 1366,\n"
"    \"height\": 697,\n"
"    \"direction\": 2,\n"
"    \"shifters\": [\n"
"      {\n"
"        \"type\": 1,\n"
"        \"width\": 1366,\n"
"        \"height\": 697,\n"
"        \"direction\": 1,\n"
"        \"shifters\": [\n"
"          {\n"
"            \"type\": 1,\n"
"            \"width\": 394,\n"
"            \"height\": 697,\n"
"            \"direction\": 2,\n"
"            \"shifters\": [\n"
"              {\n"
"                \"type\": 0,\n"
"                \"width\": 394,\n"
"                \"height\": 346,\n"
"                \"currentContent\": \"Entities\",\n"
"                \"tabs\": [\n"
"                  {\n"
"                    \"name\": \"Entities\"\n"
"                  }\n"
"                ]\n"
"              },\n"
"              {\n"
"                \"type\": 0,\n"
"                \"width\": 394,\n"
"                \"height\": 345,\n"
"                \"currentContent\": \"Reactions\",\n"
"                \"tabs\": [\n"
"                  {\n"
"                    \"name\": \"Reactions\"\n"
"                  }\n"
"                ]\n"
"              }\n"
"            ]\n"
"          },\n"
"          {\n"
"            \"type\": 1,\n"
"            \"width\": 966,\n"
"            \"height\": 697,\n"
"            \"direction\": 1,\n"
"            \"shifters\": [\n"
"              {\n"
"                \"type\": 0,\n"
"                \"width\": 597,\n"
"                \"height\": 697,\n"
"                \"currentContent\": \"Simulation\",\n"
"                \"tabs\": [\n"
"                  {\n"
"                    \"name\": \"Simulation\"\n"
"                  }\n"
"                ]\n"
"              },\n"
"              {\n"
"                \"type\": 1,\n"
"                \"width\": 362,\n"
"                \"height\": 697,\n"
"                \"direction\": 2,\n"
"                \"shifters\": [\n"
"                  {\n"
"                    \"type\": 0,\n"
"                    \"width\": 362,\n"
"                    \"height\": 430,\n"
"                    \"currentContent\": \"Inspector\",\n"
"                    \"tabs\": [\n"
"                      {\n"
"                        \"name\": \"Inspector\"\n"
"                      }\n"
"                    ]\n"
"                  },\n"
"                  {\n"
"                    \"type\": 0,\n"
"                    \"width\": 362,\n"
"                    \"height\": 261,\n"
"                    \"currentContent\": \"Logger\",\n"
"                    \"tabs\": [\n"
"                      {\n"
"                        \"name\": \"Logger\"\n"
"                      },\n"
"                      {\n"
"                        \"name\": \"Warnings\"\n"
"                      }\n"
"                    ]\n"
"                  }\n"
"                ]\n"
"              }\n"
"            ]\n"
"          }\n"
"        ]\n"
"      }\n"
"    ]\n"
"  },\n"
"  \"windows\": null\n"
"}";

const char* default_nslayout = (const char*) temp_binary_data_0;


const char* getNamedResource (const char* resourceNameUTF8, int& numBytes);
const char* getNamedResource (const char* resourceNameUTF8, int& numBytes)
{
    unsigned int hash = 0;

    if (resourceNameUTF8 != nullptr)
        while (*resourceNameUTF8 != 0)
            hash = 31 * hash + (unsigned int) *resourceNameUTF8++;

    switch (hash)
    {
        case 0x1df0b56d:  numBytes = 2447; return default_nslayout;
        default: break;
    }

    numBytes = 0;
    return nullptr;
}

const char* namedResourceList[] =
{
    "default_nslayout"
};

const char* originalFilenames[] =
{
    "default.nslayout"
};

const char* getNamedResourceOriginalFilename (const char* resourceNameUTF8);
const char* getNamedResourceOriginalFilename (const char* resourceNameUTF8)
{
    for (unsigned int i = 0; i < (sizeof (namedResourceList) / sizeof (namedResourceList[0])); ++i)
        if (strcmp (namedResourceList[i], resourceNameUTF8) == 0)
            return originalFilenames[i];

    return nullptr;
}

}

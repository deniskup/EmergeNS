/* ==================================== JUCER_BINARY_RESOURCE ====================================

   This is an auto-generated file: Any edits you make may be overwritten!

*/

#include <cstring>

namespace BinaryData
{

//================== default.nslayout ==================
static const unsigned char temp_binary_data_0[] =
"{\r\n"
"  \"mainLayout\": {\r\n"
"    \"type\": 1,\r\n"
"    \"width\": 1366,\r\n"
"    \"height\": 697,\r\n"
"    \"direction\": 2,\r\n"
"    \"shifters\": [\r\n"
"      {\r\n"
"        \"type\": 1,\r\n"
"        \"width\": 1366,\r\n"
"        \"height\": 697,\r\n"
"        \"direction\": 1,\r\n"
"        \"shifters\": [\r\n"
"          {\r\n"
"            \"type\": 1,\r\n"
"            \"width\": 394,\r\n"
"            \"height\": 697,\r\n"
"            \"direction\": 2,\r\n"
"            \"shifters\": [\r\n"
"              {\r\n"
"                \"type\": 0,\r\n"
"                \"width\": 394,\r\n"
"                \"height\": 346,\r\n"
"                \"currentContent\": \"Entities\",\r\n"
"                \"tabs\": [\r\n"
"                  {\r\n"
"                    \"name\": \"Entities\"\r\n"
"                  }\r\n"
"                ]\r\n"
"              },\r\n"
"              {\r\n"
"                \"type\": 0,\r\n"
"                \"width\": 394,\r\n"
"                \"height\": 345,\r\n"
"                \"currentContent\": \"Reactions\",\r\n"
"                \"tabs\": [\r\n"
"                  {\r\n"
"                    \"name\": \"Reactions\"\r\n"
"                  }\r\n"
"                ]\r\n"
"              }\r\n"
"            ]\r\n"
"          },\r\n"
"          {\r\n"
"            \"type\": 1,\r\n"
"            \"width\": 966,\r\n"
"            \"height\": 697,\r\n"
"            \"direction\": 1,\r\n"
"            \"shifters\": [\r\n"
"              {\r\n"
"                \"type\": 0,\r\n"
"                \"width\": 597,\r\n"
"                \"height\": 697,\r\n"
"                \"currentContent\": \"Simulation\",\r\n"
"                \"tabs\": [\r\n"
"                  {\r\n"
"                    \"name\": \"Simulation\"\r\n"
"                  }\r\n"
"                ]\r\n"
"              },\r\n"
"              {\r\n"
"                \"type\": 1,\r\n"
"                \"width\": 362,\r\n"
"                \"height\": 697,\r\n"
"                \"direction\": 2,\r\n"
"                \"shifters\": [\r\n"
"                  {\r\n"
"                    \"type\": 0,\r\n"
"                    \"width\": 362,\r\n"
"                    \"height\": 430,\r\n"
"                    \"currentContent\": \"Inspector\",\r\n"
"                    \"tabs\": [\r\n"
"                      {\r\n"
"                        \"name\": \"Inspector\"\r\n"
"                      }\r\n"
"                    ]\r\n"
"                  },\r\n"
"                  {\r\n"
"                    \"type\": 0,\r\n"
"                    \"width\": 362,\r\n"
"                    \"height\": 261,\r\n"
"                    \"currentContent\": \"Logger\",\r\n"
"                    \"tabs\": [\r\n"
"                      {\r\n"
"                        \"name\": \"Logger\"\r\n"
"                      },\r\n"
"                      {\r\n"
"                        \"name\": \"Warnings\"\r\n"
"                      }\r\n"
"                    ]\r\n"
"                  }\r\n"
"                ]\r\n"
"              }\r\n"
"            ]\r\n"
"          }\r\n"
"        ]\r\n"
"      }\r\n"
"    ]\r\n"
"  },\r\n"
"  \"windows\": null\r\n"
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
        case 0x1df0b56d:  numBytes = 2547; return default_nslayout;
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

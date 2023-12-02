/* no fs */

#include <cstring>
#include <stdio.h>
#include <cstdlib>

typedef unsigned char uint8_t;
typedef short int16_t;
typedef unsigned short uint16_t;
typedef int int32_t;
typedef unsigned int uint32_t;
typedef unsigned long long int uint64_t;
typedef unsigned int uintptr_t;
typedef long unsigned int size_t;

#define MB 1000000
#define SECTOR_SIZE 512
#define DISK_SIZE 50 * MB
#define NODE_SIZE 10 * SECTOR_SIZE
#define NODE_LIST_COUNT 10000

static uint8_t virtual_disk[DISK_SIZE];

void read_sector(uint32_t sector, char* data, uint32_t size)
{
    if (size > 512)
        return;
    memcpy(data, virtual_disk + sector * 512, size);
}

void write_sector(uint32_t sector, const char* data, uint32_t size)
{
    if (size > 512)
        return;
    memcpy(virtual_disk + sector * 512, data, size);
}

void write_data(uint32_t sector, const char* data, uint32_t size)
{
    if (size <= 512)
        return write_sector(sector, data, size);

    while (size >= 512) {
        write_sector(sector, data, 512);
        sector++;
        size -= 512;
    }

    write_sector(sector, data, size);
}

void read_data(uint32_t sector, char* data, uint32_t size)
{
    if (size <= 512)
        return read_sector(sector, data, size);

    char* data_ptr = data;
    while (size >= 512) {
        read_sector(sector, data_ptr, 512);
        sector++;
        data_ptr += 512;
        size -= 512;
    }

    read_sector(sector, data, size);
}

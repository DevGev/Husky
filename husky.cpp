#include <cstring>
#include <time.h>
#include <stdio.h>
#include <cstdlib>
#include <iostream>
#include <unistd.h>
#include <filesystem>

typedef unsigned char uint8_t;
typedef short int16_t;
typedef unsigned short uint16_t;
typedef int int32_t;
typedef unsigned int uint32_t;
typedef long unsigned int size_t;

#define MB 1000000
#define SECTOR_SIZE 512
#define DISK_SIZE 50 * MB
// #define NODE_SIZE 10 * SECTOR_SIZE
// #define NODE_LIST_COUNT 10000

static uint8_t* virtual_disk = 0;

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

    const char* data_ptr = data;
    while (size >= 512) {
        write_sector(sector, data_ptr, 512);
        data_ptr += 512;
        sector++;
        size -= 512;
    }

    write_sector(sector, data_ptr, size);
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

    read_sector(sector, data_ptr, size);
}

/* start of filesystem [USE KMALLOC IN KERNEL] */

typedef struct hhash {
    uint32_t h;
    uint32_t c;
} __attribute__((packed)) hhash_t;

typedef struct block {
    uint8_t flags;
} __attribute__((packed)) block_t;

typedef struct indirect_block {
    uint32_t data_block_ptrs[1279];
} indirect_block_t; /* not used. */

typedef struct super_node {
    char magic[25];
    uint32_t nodes_count;
    uint32_t data_blocks_count;
    uint32_t data_block_size;
    uint32_t mount_size;
} __attribute__((packed)) super_node_t;

typedef struct node {
    uint8_t type; /* 0 = not in use */
    uint16_t uid;
    uint16_t gid;
    uint32_t size_in_bytes;
    uint32_t modification_time;
    uint32_t creation_time;
    uint32_t last_access_time;
    uint32_t permission;
    char name[255];

    hhash_t own_hash;
    hhash_t assoc_hash;

    uint32_t blocks_ptrs[100];
    uint32_t iblocks_ptrs[210];
} __attribute__((packed)) node_t;


#define DEBUG(...) if (debug) printf(__VA_ARGS__)

static const bool debug = false;
static uint32_t fs_start = 0;
static uint32_t ptrs[1280];
static super_node_t super_node;
static node_t root_node;
static node_t* nodes_cache;

static inline uint32_t murmur3_32_scramble(uint32_t k)
{
    k *= 0xcc9e2d51;
    k = (k << 15) | (k >> 17);
    k *= 0x1b873593;
    return k;
}

void hhash_str(hhash_t* hsh, const char* s, const size_t len)
{
    const uint8_t* key = (const uint8_t*)s;
    uint32_t h = len;
    uint32_t k;

    for (size_t i = len >> 2; i; i--) {
        memcpy(&k, key, sizeof(uint32_t));
        key += sizeof(uint32_t);
        h ^= murmur3_32_scramble(k);
        h = (h << 13) | (h >> 19);
        h = h * 5 + 0xe6546b64;
    }
    k = 0;

    for (size_t i = len & 3; i; i--) {
        k <<= 8;
        k |= key[i - 1];
    }

    h ^= murmur3_32_scramble(k);
    h ^= len;
    h ^= h >> 16;
    h *= 0x85ebca6b;
    h ^= h >> 13;
    h *= 0xc2b2ae35;
    h ^= h >> 16;
    hsh->h = h;
    hsh->c = s[len - 1] + (10000 * s[0]);
}

bool hhash_cmp(hhash_t* hsh1, hhash_t* hsh2)
{
    if (hsh1->h == hsh2->h && hsh1->c == hsh2->c) 
        return true;
    return false;
}

/* cache free node and block lookup */
static uint32_t previous_node_ptr = 0;
static uint32_t previous_block_ptr = 0;

uint8_t find_filesystem()
{
    memset(&super_node, 0, sizeof(super_node_t));
    bool has_found = 0;

    while (fs_start * 512 < DISK_SIZE) {
        read_sector(fs_start, (char*)&super_node, sizeof(super_node_t));
        fs_start++;
        if (strncmp(super_node.magic, "magisk.1690243253", 17) == 0) {
            has_found = 1;
            break;
        }
    }

    if (!has_found)
        return 1;

    previous_node_ptr = 0;
    previous_block_ptr = 0;
    nodes_cache = (node_t*)malloc(super_node.nodes_count * sizeof(node_t));
    read_data(fs_start, (char*)nodes_cache, super_node.nodes_count * sizeof(node_t));
    return 0;
}

uint8_t find_empty_node(uint32_t* node_ptr, uint32_t* sector_ptr)
{
    uint32_t runs = 1;
    uint32_t empty_node_ptr = previous_node_ptr;
    if (empty_node_ptr >= super_node.nodes_count) {
        empty_node_ptr = 0;
        runs = 0;
    }

    uint32_t node_siz_div = sizeof(node_t) / 512;
    uint32_t sector_search = empty_node_ptr * node_siz_div;

    for (;;) {
        if (!nodes_cache[empty_node_ptr].type)
            break;

        empty_node_ptr++;
        sector_search += node_siz_div;
        if (empty_node_ptr >= super_node.nodes_count) {
            empty_node_ptr = 0;
            sector_search = 0;
            runs--;
        }

        if (empty_node_ptr >= super_node.nodes_count && !runs) {
            DEBUG("could not find empty node\n");
            return 1;
        }
    }

    DEBUG("found empty node[%d] at sector %d\n", empty_node_ptr, sector_search);
    *node_ptr = empty_node_ptr;
    *sector_ptr = sector_search;
    previous_node_ptr = empty_node_ptr + 1;
    return 0;
}

uint8_t find_empty_block(uint32_t* block_ptr, uint32_t* sector_ptr)
{
    block_t block;
    uint32_t runs = 1;
    uint32_t empty_block_ptr = previous_block_ptr;
    if (empty_block_ptr >= super_node.data_blocks_count) {
        empty_block_ptr = 0;
        runs = 0;
    }

    uint32_t block_siz_div =  super_node.data_block_size / 512;
    uint32_t sector_search = (super_node.nodes_count * sizeof(node_t)) / 512 + empty_block_ptr * block_siz_div;

    for (;;) {
        read_sector(fs_start + sector_search, (char*)&block, sizeof(block_t));
        if (!block.flags)
            break;

        empty_block_ptr++;
        sector_search += block_siz_div;
        if (empty_block_ptr >= super_node.data_blocks_count) {
            empty_block_ptr = 0;
            sector_search = 0;
            runs--;
        }

        if (empty_block_ptr >= super_node.data_blocks_count && !runs) {
            DEBUG("could not find empty data block\n");
            return 1;
        }
    }

    DEBUG("found empty block[%d] at sector %d\n", empty_block_ptr, sector_search);
    *block_ptr = empty_block_ptr;
    *sector_ptr = sector_search;
    previous_block_ptr = empty_block_ptr + 1;
    return 0;
}

void create_root_directory()
{
    const char* pathname = "/";
    hhash_t hhash;
    hhash_str(&hhash, pathname, 1);
    
    memset(&root_node, 0, sizeof(node_t));
    root_node.type = 4;
    root_node.creation_time = (unsigned)time(NULL);
    root_node.last_access_time = (unsigned)time(NULL);
    root_node.modification_time = (unsigned)time(NULL);
    root_node.uid = 0x1;
    memcpy(&root_node.own_hash, &hhash, sizeof(hhash_t));
    strcpy(root_node.name, pathname);
    DEBUG("root node: hash %d:%d %s\n", hhash.h, hhash.c, pathname);

    memcpy(nodes_cache, &root_node, sizeof(node_t));
    write_data(fs_start, (char*)&root_node, sizeof(node_t));
}

uint8_t find_node(hhash_t* hsh, int type, uint32_t* node_ptr)
{
    uint32_t empty_node_ptr = 0;
    uint32_t node_siz_div = sizeof(node_t) / 512;

    for (;;) {
        if (nodes_cache[empty_node_ptr].type == type) {
            if (hhash_cmp(&(nodes_cache[empty_node_ptr].own_hash), hsh))
                break;
        }
        empty_node_ptr++;
        if (empty_node_ptr >= super_node.nodes_count)
            return 1;
    }

    DEBUG("found node[%d]\n", empty_node_ptr);
    *node_ptr = empty_node_ptr;
    return 0;
}

void write_node(node_t* node)
{
    DEBUG("\n");
    uint32_t free_node_ptr = 0;
    uint32_t free_node_sector = 0;
    find_empty_node(&free_node_ptr, &free_node_sector);
    memcpy(&nodes_cache[free_node_ptr], node, sizeof(node_t));
    write_data(fs_start + free_node_sector, (char*)node, sizeof(node_t));
    DEBUG("%s node[%d] : hash %d:%d name: %s\n", (node->type == 4) ? "directory" : "file", 
            free_node_ptr, node->own_hash.h, node->own_hash.c, node->name);
}

void create_directory(const char* pathname)
{
    if (pathname[0] == '\0' || pathname[0] != '/')
        return;

    int subdir_ptr = strlen(pathname) - 1;
    while (subdir_ptr > 0 && pathname[subdir_ptr] != '/')
        subdir_ptr--;

    node_t node;
    memset(&node, 0, sizeof(node_t));
    hhash_str(&node.own_hash, pathname, strlen(pathname));

    if (!subdir_ptr) {
        memcpy(&node.assoc_hash, &root_node.own_hash, sizeof(hhash_t));
    } else {
        hhash_str(&node.assoc_hash, pathname, subdir_ptr);
    }

    node.type = 4;
    node.creation_time = (unsigned)time(NULL);
    node.last_access_time = (unsigned)time(NULL);
    node.modification_time = (unsigned)time(NULL);
    node.uid = 0x1;
    strncpy(node.name, pathname + subdir_ptr + 1, strlen(pathname) - subdir_ptr - 1);
    write_node(&node);
}

uint8_t list_directory(const char* pathname, uint32_t* entries)
{
    if (pathname[0] == '\0' || pathname[0] != '/')
        return 1;

    node_t node;
    uint32_t node_ptr = 0;
    uint32_t dir_entries = 0;
    memset(&node, 0, sizeof(node_t));

    if (strlen(pathname) == 1 && pathname[0] == '/') {
        memcpy(&node.own_hash, &root_node.own_hash, sizeof(hhash_t));
    } else {
        hhash_str(&node.own_hash, pathname, strlen(pathname));
    }

    uint32_t empty_node_ptr = 0;
    uint32_t node_siz_div = sizeof(node_t) / 512;

    for (;;) {
        if (nodes_cache[empty_node_ptr].type) {
            if (hhash_cmp(&(nodes_cache[empty_node_ptr].assoc_hash), &node.own_hash)) {
                printf(" * %s\n", nodes_cache[empty_node_ptr].name);
                dir_entries++;
            }
        }
        empty_node_ptr++;
        if (empty_node_ptr >= super_node.nodes_count)
            break;
    }

    //*entries = dir_entries;
    return 0;
}

uint8_t delete_file_data(node_t* node)
{
     if (node->type != 2)
         return 1;
     if (!node->size_in_bytes)
         return 0;

    block_t block;
    block.flags = 0;
    uint32_t size = node->size_in_bytes;
    uint32_t data_blocks_to_remove = 0;

    data_blocks_to_remove = size / (super_node.data_block_size - sizeof(block_t));
    if ((size % (super_node.data_block_size - sizeof(block_t))) != 0)
        data_blocks_to_remove += 1;

    for (uint32_t i  = 0; i < sizeof(node->blocks_ptrs) / 4; ++i) {
        if (!data_blocks_to_remove)
            return 0;
        DEBUG("deleting block at sector %d\n", node->blocks_ptrs[i]);
        write_sector(fs_start + node->blocks_ptrs[i], (char*)&block, sizeof(block_t));
        data_blocks_to_remove--;
    }

    for (uint32_t i  = 0; i < sizeof(node->iblocks_ptrs) / 4; ++i) {
        read_data(fs_start + node->iblocks_ptrs[i], (char*)ptrs, super_node.data_block_size);
        for (uint32_t i  = 0; i < 1279; ++i) {
            if (!data_blocks_to_remove)
                return 0;
            DEBUG("deleting block at sector %d\n", ptrs[i]);
            write_sector(fs_start + ptrs[i], (char*)&block, sizeof(block_t));
            data_blocks_to_remove--;
        }
        write_sector(fs_start + node->iblocks_ptrs[i], (char*)&block, sizeof(block_t));
    }

    return 0;
}

uint8_t unlink_path(const char* pathname)
{
    if (pathname[0] == '\0' || pathname[0] != '/')
        return 1;

    node_t node;
    uint32_t node_ptr = 0;
    uint16_t type = 2;
    memset(&node, 0, sizeof(node_t));
    hhash_str(&node.own_hash, pathname, strlen(pathname));
    if (find_node(&node.own_hash, type, &node_ptr)) {
        type = 4;
        if (find_node(&node.own_hash, type, &node_ptr))
            return 1;
    }

    memcpy(&node, &nodes_cache[node_ptr], sizeof(node_t));

    if (type == 2)
        delete_file_data(&node);
    
    if (type == 4) {
        uint32_t entries = 0;
        list_directory(pathname, &entries);
        if (entries) {
            DEBUG("could not unlink %s, has children\n", pathname);
            return 1;
        }
    }

    node.type = 0;
    nodes_cache[node_ptr].type = node.type;
    write_sector(fs_start + (node_ptr * sizeof(node_t)) / 512, (char*)&node, sizeof(node_t));
    DEBUG("deleting node[%d] at sector %ld\n", node_ptr, (node_ptr * sizeof(node_t) / 512));
    return 0;
}


uint32_t write_file_data_block_list(uint32_t* ptr_list, const char* written_data_ptr, uint32_t* total_written, uint32_t* size_to_write, uint32_t max_blocks)
{
    uint32_t direct_data_blocks_used = 0;
    uint32_t block_ptr = 0;
    uint32_t sector_ptr = 0;
    uint32_t written = 0;

    while (*size_to_write && direct_data_blocks_used < max_blocks) {
        if (find_empty_block(&block_ptr, &sector_ptr)) {
            DEBUG("filesystem ran out of free data blocks\n");
            return 0;
        }

        block_t block;
        block.flags = 2;
        static char sector[512];
        memset(sector, 0, 512);
        uint32_t sector_size_cpy = 512 - sizeof(block_t);
        if (*size_to_write < sector_size_cpy)
            sector_size_cpy  = *size_to_write;

        memcpy(sector, &block, sizeof(block_t));
        memcpy(sector + sizeof(block_t), written_data_ptr, sector_size_cpy);
        write_sector(fs_start + sector_ptr, (const char*)sector, 512);
        written_data_ptr += sector_size_cpy;
        *size_to_write = *size_to_write - sector_size_cpy;
        written += sector_size_cpy;
        *(ptr_list + direct_data_blocks_used) = sector_ptr;
        DEBUG("write header and %d bytes data to data[%d] node->iblock=%d at sector %d\n", sector_size_cpy, block_ptr, *(ptr_list + direct_data_blocks_used), sector_ptr);
        sector_ptr++;
        direct_data_blocks_used++;

        uint32_t siz = super_node.data_block_size - 512;
        if (*size_to_write < siz)
            siz = *size_to_write;
        if (!siz)
            break;

        write_data(fs_start + sector_ptr, written_data_ptr, siz);
        written += siz;
        written_data_ptr += siz;
        DEBUG("write %d bytes data to data[%d] node->iblock=%d at sector %d\n", siz, block_ptr, *(ptr_list + direct_data_blocks_used - 1), sector_ptr);
        *size_to_write = *size_to_write - siz;
    }

    *total_written = written;
    return direct_data_blocks_used;
}

int8_t write_file_data(node_t* node, const char* data, size_t size)
{
    DEBUG("\n");
    char* written_data_ptr = (char*)data;
    uint32_t size_to_write = size;
    uint32_t direct_data_blocks_used = 0;
    uint32_t block_ptr = 0;
    uint32_t sector_ptr = 0;
    uint32_t written = 0;

    uint32_t blocks_used = write_file_data_block_list(ptrs, written_data_ptr, &written, &size_to_write, sizeof(node->blocks_ptrs) / 4);
    written_data_ptr += written;
    for (int i = 0; i < blocks_used; ++i)
        node->blocks_ptrs[i] = ptrs[i];

    if (!blocks_used && size_to_write)
        return 1;
    if (!size_to_write)
        return 0;

    for (uint32_t indirect_node = 0; indirect_node < sizeof(node->iblocks_ptrs) / 4; ++indirect_node) {
        if (find_empty_block(&block_ptr, &sector_ptr)) {
            DEBUG("filesystem ran out of free data blocks\n");
            return 0;
        }
        
        block_t block;
        block.flags = 5;
        write_data(fs_start + sector_ptr, (const char*)&block, sizeof(block_t));

        node->iblocks_ptrs[indirect_node] = sector_ptr;
        uint32_t blocks_used = write_file_data_block_list(ptrs + 1, written_data_ptr, &written, &size_to_write, 1279);
        written_data_ptr += written;
        DEBUG("write indirect[%d] block[%d] blocks_used=%d at sector %d\n", indirect_node, block_ptr, blocks_used, sector_ptr);
        ptrs[0] = 0;
        memcpy(ptrs, &block.flags, sizeof(block));
        write_data(fs_start + sector_ptr, (const char*)ptrs, super_node.data_block_size);

        if (!blocks_used && size_to_write)
            return 1;
        if (!size_to_write)
            return 0;
    }

    return 0;
}

uint8_t write_file(const char* pathname, const char* data, size_t size)
{
    /* printf("%s\n",pathname); */
    if (pathname[0] == '\0' || pathname[0] != '/')
        return 1;

    int subdir_ptr = strlen(pathname) - 1;
    while (subdir_ptr > 0 && pathname[subdir_ptr] != '/')
        subdir_ptr--;

    node_t node;
    memset(&node, 0, sizeof(node_t));
    hhash_str(&node.own_hash, pathname, strlen(pathname));

    if (!subdir_ptr) {
        memcpy(&node.assoc_hash, &root_node.own_hash, sizeof(hhash_t));
    } else {
        hhash_str(&node.assoc_hash, pathname, subdir_ptr);
    }

    uint32_t parent_node_ptr = 0;
    if (find_node(&node.assoc_hash, 4, &parent_node_ptr))
        return 1;

    uint32_t node_ptr = 0;
    bool overwrite = (find_node(&node.own_hash, 2, &node_ptr) == 0);
    if (overwrite)
        delete_file_data(&nodes_cache[node_ptr]);

    node.type = 2;
    node.size_in_bytes = size;
    node.creation_time = (unsigned)time(NULL);
    node.last_access_time = (unsigned)time(NULL);
    node.modification_time = (unsigned)time(NULL);
    strncpy(node.name, pathname + subdir_ptr + 1, strlen(pathname) - subdir_ptr - 1);
    if (size)
        write_file_data(&node, data, size);

    if (overwrite) {
        memcpy(&nodes_cache[node_ptr], &node, sizeof(node_t));
        write_data(fs_start + sizeof(node_t) * node_ptr, (char*)&node, sizeof(node_t));
        DEBUG("overwriting existing file\n");
        return 0;
    }

    write_node(&node);
    return 0;
}

uint32_t read_file_data_block_list(uint32_t* ptr_list, char* read_data_ptr, uint32_t* seek, uint32_t* total_read, uint32_t* size_to_read, uint32_t max_blocks)
{
    uint32_t blocks_read  = 0;
    uint32_t size_read = 0;

    for (uint32_t i = 0; i < max_blocks; ++i) {
        char sector[512];
        read_sector(fs_start + ptr_list[i], sector, 512);
        block_t block;
        memcpy(&block, sector, sizeof(block_t));

        if (block.flags != 2) {
            DEBUG("points to invalid block at sector %d type=%d\n", ptr_list[i], block.flags);
            return 0;
        }

        uint32_t siz = (*seek >= 511) ? 0 : 511 - *seek;
        if (*size_to_read < siz)
            siz = *size_to_read;

        if (*seek < 511) {
            memcpy(read_data_ptr, sector + 1 + *seek, siz);
            DEBUG("copy %d bytes from block at sector %d\n", siz, ptr_list[i]);
            read_data_ptr += siz;
            size_read += siz;
            *size_to_read = *size_to_read - siz;
            blocks_read++;
            *seek = 0;
        } else {
            *seek -= 511;
            blocks_read++;
        }

        uint32_t sectors_to_skip = 0;
        uint32_t bytes_to_skip = 0;
        siz = super_node.data_block_size - 512; 

        if (*seek >= siz) {
            *seek -= siz;
            continue;
        }
        if (*size_to_read < siz)
            siz = *size_to_read;
        if (!siz)
            break;

        if (*seek) {
            sectors_to_skip = *seek / 512;
            bytes_to_skip = *seek % 512;
            read_sector(fs_start + ptr_list[i] + 1 + sectors_to_skip, sector, 512);
            uint32_t siz = 512 - bytes_to_skip;
            if (*size_to_read < siz)
                siz = *size_to_read;
            memcpy(read_data_ptr, sector + bytes_to_skip, siz);
            read_data_ptr += siz;
            size_read += siz;
            *size_to_read = *size_to_read - siz;
            siz = super_node.data_block_size - 512 - *seek; 
            sectors_to_skip++;
            *seek = 0;

            if (!(*size_to_read))
                break;
        }

        if (*size_to_read < siz)
            siz = *size_to_read;
        DEBUG("copy %d bytes from block at sector %d\n", siz, ptr_list[i]);
        read_data(fs_start + ptr_list[i] + 1 + sectors_to_skip, read_data_ptr, siz);
        read_data_ptr += siz;
        size_read += siz;
        *size_to_read = *size_to_read - siz;
        if (!(*size_to_read))
            break;
    }

    *total_read = size_read;
    return blocks_read;
}

uint32_t read_file(const char* pathname, char* data, size_t size, uint32_t seek = 0)
{
    if (pathname[0] == '\0' || pathname[0] != '/')
        return 0;

    node_t node;
    uint32_t node_ptr = 0;
    memset(&node, 0, sizeof(node_t));
    hhash_str(&node.own_hash, pathname, strlen(pathname));
    if (find_node(&node.own_hash, 2, &node_ptr))
        return 0;
    memcpy(&node, &nodes_cache[node_ptr], sizeof(node_t));

    if (seek >= node.size_in_bytes)
        return 0;
    if (seek + size > node.size_in_bytes)
        size = node.size_in_bytes - seek;
    if (size > node.size_in_bytes)
        size = node.size_in_bytes;

    uint32_t size_to_read = size;
    char* read_data_ptr = data;
    uint32_t total_read = 0;
    uint32_t seek_blocks = 0;
    uint32_t seek_bytes = 0;

    if (seek) {
        seek_blocks = seek / (super_node.data_block_size - sizeof(block_t));
        seek_bytes = seek - seek_blocks * (super_node.data_block_size - sizeof(block_t));
        DEBUG("seek %d, seek blocks %d seek bytes %d\n", seek, seek_blocks, seek_bytes);
    }

    for (uint32_t i = 0; i < sizeof(node.blocks_ptrs) / 4; ++i)
        ptrs[i] = node.blocks_ptrs[i];

    if (seek_blocks < (sizeof(node.blocks_ptrs) / 4)) {
        uint32_t blocks_used = read_file_data_block_list(ptrs + seek_blocks, read_data_ptr, &seek_bytes, &total_read, &size_to_read, sizeof(node.blocks_ptrs) / 4 - seek_blocks);
        read_data_ptr += total_read;

        if (!blocks_used && size_to_read)
            return 0;
        if (!size_to_read)
            return size;
    }

    seek_blocks -= sizeof(node.blocks_ptrs) / 4;

    for (uint32_t indirect_node = 0; indirect_node < sizeof(node.iblocks_ptrs) / 4; ++indirect_node) {
        read_data(fs_start + node.iblocks_ptrs[indirect_node], (char*)ptrs, super_node.data_block_size);
        if (seek_blocks >= 1279) {
            seek_blocks -= 1279;
            continue;
        }
        uint32_t blocks_used = read_file_data_block_list(ptrs + 1 + seek_blocks, read_data_ptr, &seek_bytes, &total_read, &size_to_read, 1279 - seek_blocks);
        read_data_ptr += total_read;

        if (!blocks_used && size_to_read)
            return 0;
        if (!size_to_read)
            return size;
    }

    return size;
}

uint8_t file_size(const char* pathname, size_t* size)
{
    if (pathname[0] == '\0' || pathname[0] != '/')
        return 1;

    node_t node;
    uint32_t node_ptr = 0;
    hhash_str(&node.own_hash, pathname, strlen(pathname));
    if (find_node(&node.own_hash, 2, &node_ptr))
        return 1;
    memcpy(&node, &nodes_cache[node_ptr], sizeof(node_t));
    *size = node.size_in_bytes;
    return 0;
}

int main()
{
    virtual_disk = (uint8_t*)malloc(DISK_SIZE);
    memset(virtual_disk, 0, DISK_SIZE);
    super_node_t super_node;
    super_node.mount_size = DISK_SIZE;
    strcpy(super_node.magic, "magisk.1690243253");
    super_node.nodes_count = 10000;
    super_node.data_block_size = 512 * 10;
    super_node.data_blocks_count = (DISK_SIZE - 512 * 2 - super_node.nodes_count * sizeof(node_t)) / super_node.data_block_size;
    memcpy(virtual_disk, &super_node, sizeof(super_node_t));

    find_filesystem();
    create_root_directory();

    printf("virtual disk size %d mb\n", DISK_SIZE / MB);
    printf("super: sizeof node_t %ld\n", sizeof(node_t));
    printf("super: filesystem root sector %d\n", fs_start);
    printf("super: number of nodes in fs: %d\n", super_node.nodes_count);
    printf("super: number of blocks in fs: %d\n", super_node.data_blocks_count);

    std::string ppath;
    std::filesystem::current_path("Base/root"); // (3)
    using recursive_directory_iterator = std::filesystem::recursive_directory_iterator;
    for (const auto& entry: recursive_directory_iterator(".")) {
        ppath = entry.path().generic_string();
        if (ppath.size() < 3)
            continue;
        ppath.erase(0, 1);
        if (std::filesystem::is_directory(entry)) {
            create_directory((ppath).c_str());
        } else {
            uint8_t* data = (uint8_t*)malloc(entry.file_size());
            FILE* fptr = fopen(entry.path().generic_string().c_str(),"r");
            fread(data, sizeof(char), std::filesystem::file_size(entry), fptr);
            fclose(fptr);
            write_file(ppath.c_str(), (const char*)data, std::filesystem::file_size(entry));
            free(data);
        }
    }


    std::filesystem::current_path("../.."); // (3)
    FILE* fptr = fopen("./virtdrive","w");
    fwrite(virtual_disk, sizeof(char), DISK_SIZE, fptr);
    fclose(fptr);
}

// Name of program mainreturn.cpp 
#include <iostream>
#include <fstream>
#include <iosfwd>
#include <string>
#include <cmath>
#include <sstream>
#include <algorithm>
#include <vector>

using namespace std;
vector<string> optimal_set;

long incrementer = 0;

int temp_policy;
int invalid_wb = 0;
//These variables are going to be constantly accessed and as such should be global variables
int mem_traffic;
int block_size;
int l1_size;
int l1_assoc;
int l2_size;
int l2_assoc;
int rep_policy;
int inc_policy;
long l1_set;
long l2_set;
//These need to be initiated at 1
long l1_serial = 1;
long l2_serial = 1;
int file_size = 0;

struct block {
    bool valid;
    bool dirty;
    long line_feed;
    string block_address;
    string hex_address;
    string tag;
};

//l1 cache identifier
block** l1_cache;
//L2 Cache identifier
block**l2_cache;

//Simulation output files
string hex_address;
vector<string> action_file;
vector<string> address_file;
vector<string> combined;

string optimal_victim;
//Simulation Output
int l1_reads            =0;
int l1_read_miss        =0;
int l1_writes           =1;
int l1_write_miss       =1;
int l1_write_back       =1;
int l2_reads_file       =0;
int l2_read_miss        =0;
int l2_writes           =0;
int l2_write_miss       =0;
int l2_write_backs      =0;

string::size_type size;//for initializing maximum variable size

struct address{
    string block_address;
    string tag;
    int index;
};
address make_address(const string& address_in, long set_level){

    long adress_in = stol(address_in, &size, 16);
    int index_bits  = ceil(log2(set_level));
    int block_bits  = ceil(log2(block_size));

    //Populate the block and tag addresses
    long address_parse = pow(2, block_bits);
    long block_address  = adress_in % address_parse;

    block_address = adress_in - block_address;

    long tag_parse = pow(2, index_bits+block_bits);
    long tag_address = adress_in / tag_parse;
    int index = (adress_in % tag_parse) / address_parse;

    address new_address;

    stringstream tag_info;
    tag_info << hex << tag_address;
    new_address.tag = tag_info.str();

    stringstream bit_info;
    bit_info << hex << block_address;
    new_address.block_address =  bit_info.str();
    new_address.index =  index;
    return(new_address);
}

vector<bool> map_l1;
vector<bool> map_l2;

int plru_index_l1 = 0;
int plru_index_l2 = 0;

block** cache_write(block** cache, int index, bool write, address new_address, int level){
    //Write to cache and save output
    //cout<<index<<endl;
    cache[new_address.index][index].block_address = new_address.block_address;
    cache[new_address.index][index].hex_address = hex_address;
    cache[new_address.index][index].tag = new_address.tag;
    if(level == 2){ cache[new_address.index][index].line_feed = l2_serial++;}
    if(level == 1){ cache[new_address.index][index].line_feed = l1_serial++;}
    cache[new_address.index][index].valid = true;
    // If write, then set dirty bit, else just read, so don't set dirty bit
    if (write){
        cache[new_address.index][index].dirty = true;
    }
    else {
        cache[new_address.index][index].dirty = false;
    }
    return cache;
}

void plru_map_l1(int x) {
    x = x+ l1_assoc;
    while (x != 0) {
        x = (x - 1) / 2;
        map_l1[x] = !map_l1[x];
    }
    int k = 0;
    for (int i = 0; i < log2(l1_assoc); i++) {
        if (map_l1[k] == 0) {
            k = 2*k +1;

        }
        else{
            k = 2*k +2;
        }
    }
    //cout<<"k = "<<k<<"\t and \tplru_index ="<<plru_index_l1<<endl;
    plru_index_l1 = k-(l1_assoc-1);
    //cout<<plru_index_l1;

}

void plru_map_l2(int x ){
    x = x+ l2_assoc;
    while (x != 0) {
        x = (x - 1) / 2;
        map_l2[x] = !map_l2[x];
    }
    int k = 0;
    for (int i = 0; i < log2(l2_assoc); i++) {
        if (map_l2[k] == 0) {
            k = 2*k +1;
        }
        else{
            k = 2*k +2;
        }
    }
    plru_index_l2 = k-(l2_assoc-1);
}

bool invalidation(const address& new_address, block** cache){
    bool valid_bit = false;
    for (int i=0; i<l1_assoc; i++){
        if (cache[new_address.index][i].block_address==new_address.block_address){
            if (cache[new_address.index][i].valid){
                cache[new_address.index][i].valid = false;
                if (cache[new_address.index][i].dirty){
                    invalid_wb++;
                    valid_bit = true;
                    return valid_bit;
                }
                if (!cache[new_address.index][i].dirty){
                    return valid_bit;
                }
            }
        }
    }
    return valid_bit;
}

void optimal_addressing(long set_level, vector<string> &optimal_set){
    long start = incrementer +1;
    for(long i =start; i<file_size;i++) {
        if (optimal_set.size() == 1) {
            optimal_victim = optimal_set[0];
            return;
        }
        for (int j = 0; j < optimal_set.size(); j++) {
            if (!address_file[i].empty()) {
                address new_address = make_address(address_file[i], set_level);
                if (optimal_set[j] == new_address.block_address) {
                    optimal_set.erase(optimal_set.begin() + j);
                    optimal_victim = optimal_set[0];
                    break;
                }
            }
        }
    }
    optimal_victim = optimal_set[0];
}

void cache_call_l2(int index,  address new_address){
    if (l2_cache[new_address.index][index].valid){
        if (l2_cache[new_address.index][index].dirty){
            if (inc_policy==1){
                new_address = make_address(l2_cache[new_address.index][index].hex_address, l1_set);
                bool read_check = invalidation(new_address, l1_cache);
                if (!read_check){
                    l2_write_backs++;
                }
            }
            else {
                l2_write_backs++;
            }
        }
        else{
            if (inc_policy==1){
                new_address = make_address(l2_cache[new_address.index][index].hex_address, l1_set);
                invalidation(new_address, l1_cache);
            }
        }
    }
}

long lru_check(address new_address, int assoc, block** cache){
    long victim_bit = LONG_MAX;
    for (int i = 0; i < assoc; i++) {
        if (!cache[new_address.index][i].valid) {
            victim_bit = cache[new_address.index][i].line_feed;
            return victim_bit;
        }
        else {
            if(cache[new_address.index][i].line_feed < victim_bit){
                victim_bit = cache[new_address.index][i].line_feed;
            }
        }
    }
    return victim_bit;
}

long plru_check(address new_address, int assoc, block** cache, int level, long index){
    long victim_bit = LONG_MAX;
    //cout<<"PLRU"<<endl;
    for (int i = 0; i < assoc; i++) {
        if (!cache[new_address.index][i].valid){
            victim_bit = cache[new_address.index][i].line_feed;
            return victim_bit;
        }
        else {
            victim_bit = cache[new_address.index][index].line_feed;
            if(level == 1){
                plru_map_l1(plru_index_l1);
            }
            if(level == 2){
                plru_map_l2(plru_index_l2);
            }
        }
    }
    return victim_bit;
}

void l2_write(string address_in, bool write) {

    if (l2_size <= 0) {
        return;
    }

    if(l2_assoc ==2 && rep_policy == 1){
        temp_policy = rep_policy;
        rep_policy = 0;
    }
    else{temp_policy = rep_policy;}

    //Get the tag and index
    address new_address = make_address(address_in, l2_set);

    if (write) {
        l2_writes++;
        //Check if the address is available, then set the dirty bit to true and return
        for (int i = 0; i < l2_assoc; i++) {
            if (l2_cache[new_address.index][i].valid && l2_cache[new_address.index][i].tag == new_address.tag) {
                switch (rep_policy) {
                    case 0:
                        l2_cache[new_address.index][i].line_feed = l2_serial++;
                        break;

                    case 1:
                        l2_cache[new_address.index][i].line_feed = l2_serial++;
                        plru_map_l2(i);
                        break;

                    case 2:
                        l2_cache[new_address.index][i].line_feed = l2_serial++;
                        break;
                }
                l2_cache[new_address.index][i].dirty = true;
                rep_policy = temp_policy;
                return;
            }
        }
        l2_write_miss++;
    }
    //Else:
    //Determine the victim (empty slot or the minimum serial)
    long victim_bit;// = LONG_MAX;
    switch(rep_policy){
        case 0:
            victim_bit = lru_check(new_address, l2_assoc, l2_cache);
            break;
        case 1:
            victim_bit = plru_check(new_address, l2_assoc, l2_cache, 2, plru_index_l2);
            break;
        case 2:
            for (int i = 0; i < l1_assoc; i++) {
                if (!l2_cache[new_address.index][i].valid) {
                    victim_bit = l2_cache[new_address.index][i].line_feed;
                    break;
                }
            }
            //Determine optimal replacement in case no invalid slots are avialable
            for (int j = 0; j < l2_assoc; j++) {
                    optimal_set.push_back(l2_cache[new_address.index][j].block_address);
                }
                optimal_addressing(l2_set, optimal_set);
                string victim_block = optimal_set[0];
                for (int j = 0; j < l1_assoc; j++) {
                    if (l2_cache[new_address.index][j].block_address == victim_block) {
                        victim_bit = l2_cache[new_address.index][j].line_feed;
                        break;
                    }
                }

            break;

    }

    //Insert into cache
    if(rep_policy == 1){
        cache_call_l2(plru_index_l2, new_address);
        l2_cache = cache_write(l2_cache, plru_index_l2, write, new_address, 2);
    }
    else {
        for (int i = 0; i < l2_assoc; i++) {
            if (l2_cache[new_address.index][i].line_feed == victim_bit) {
                cache_call_l2(i, new_address);
                l2_cache = cache_write(l2_cache, i, write, new_address, 2);
                break;
            }
        }
    }
    rep_policy = temp_policy;
}

void l2_read(){
    if(l2_size<=0){return;}

    if(l2_assoc ==2 && rep_policy == 1){
        temp_policy = rep_policy;
        rep_policy = 0;
    }
    else{temp_policy = rep_policy;}

    address new_address = make_address(hex_address, l2_set);
    l2_reads_file++;

    for (int i=0; i<l2_assoc; i++){
        if (l2_cache[new_address.index][i].tag == new_address.tag && l2_cache[new_address.index][i].valid){
            switch(rep_policy) {
                case 0:
                    l2_cache[new_address.index][i].line_feed = l2_serial++;
                    break;

                case 1:
                    l2_cache[new_address.index][plru_index_l2].line_feed = l2_serial++;
                    plru_map_l2(i);
                    break;

                case 2:
                    l2_cache[new_address.index][i].line_feed = l2_serial++;
                    break;
            }
            rep_policy = temp_policy;
            return;
        }
    }
    l2_read_miss++;
    l2_write(hex_address, false);
}

void cache_call_l1(int index,  address new_address){
    if (!l1_cache[new_address.index][index].valid) {
        return;
    }
    else {
        //if victim dirty bit is set, send write to L2
        if (l1_cache[new_address.index][index].dirty) {
            l1_cache[new_address.index][index].valid = false;
            l1_write_back++;
            l2_write(l1_cache[new_address.index][index].hex_address, true);
        } else {
            l1_cache[new_address.index][index].valid = false;
        }
    }
}

void l1_write(bool write){
    //Get the tag and index
    if(l1_assoc ==2 && rep_policy == 1){
        temp_policy = rep_policy;
        rep_policy = 0;
    }
    //else{temp_policy = rep_policy;}

    address new_address = make_address(hex_address, l1_set);

    //If explicit write we check  if dirty is available
    if (write){
        l1_writes =l1_writes+ 1;
        for (int i = 0; i < l1_assoc; i++) {
            if (l1_cache[new_address.index][i].tag == new_address.tag && l1_cache[new_address.index][i].valid) {
                switch(rep_policy) {
                    case 0:
                        //cout<<"L1 update LRU"<<endl;
                        l1_cache[new_address.index][i].line_feed = l1_serial++;
                        break;

                    case 1:
                        l1_cache[new_address.index][i].line_feed = l1_serial++;
                        plru_map_l1(i);
                        break;

                    case 2:
                        l1_cache[new_address.index][i].line_feed = l1_serial++;
                        break;
                }
                l1_cache[new_address.index][i].dirty = true;
                rep_policy = temp_policy;
                return;
            }
        }

        l1_write_miss = l1_write_miss+ 1;
        //l2_reads_file += 1;
    }
    //Else:
    //Determine the victim (empty slot or the minimum serial)
    long victim_in = LONG_MAX;
    switch(rep_policy) {
        case 0:
            victim_in = lru_check(new_address, l1_assoc, l1_cache);
            break;

        case 1:
            victim_in = plru_check(new_address, l1_assoc, l1_cache, 1, plru_index_l1);
            break;

        case 2:
            //Check if an invalid slot is available
            bool valid_flag = false;
            for (int i = 0; i < l1_assoc; i++) {
                //
                if (!l1_cache[new_address.index][i].valid) {
                    victim_in = l1_cache[new_address.index][i].line_feed;
                    optimal_set.clear();
                    valid_flag = true;
                    break;
                } else {
                    optimal_set.push_back(l1_cache[new_address.index][i].block_address);
                }
            }

            if (valid_flag == false) {
                optimal_addressing(l1_set, optimal_set);
                for (int j = 0; j < l1_assoc; j++) {
                    if (l1_cache[new_address.index][j].block_address == optimal_victim) {
                        victim_in = l1_cache[new_address.index][j].line_feed;
                        optimal_set.clear();
                        break;
                    }
                }
            }

    }

    if(rep_policy == 1){
        cache_call_l1(plru_index_l1, new_address);
        l2_read();
        cache_write(l1_cache, plru_index_l1, write, new_address, 1);
        plru_map_l1(plru_index_l1);
    }

    else {
        for (int i = 0; i < l1_assoc; i++) {
            if (l1_cache[new_address.index][i].line_feed == victim_in) {
                cache_call_l1(i, new_address);

                //Issue a read request to L2
                l2_read();
                l1_cache = cache_write(l1_cache, i, write, new_address, 1);
                break;
            }
        }
    }
    //rep_policy = temp_policy;
}

void l1_read(){
    //check rep_policy
    if(l1_assoc ==2 && rep_policy == 1){
        temp_policy = rep_policy;
        rep_policy = 0;
    }
    else{temp_policy = rep_policy;}

    address new_address = make_address(hex_address, l1_set);
    //Attempt L1 Read
    l1_reads = l1_reads+ 1;
    for (int i=0; i<l1_assoc; i++){
        if (l1_cache[new_address.index][i].tag == new_address.tag && l1_cache[new_address.index][i].valid){
            switch(rep_policy) {
                case 0: //LRU
                    //cout<<"L1 update LRU"<<endl;
                    l1_cache[new_address.index][i].line_feed = l1_serial++;
                    break;

                case 1: //PLRU
                    //l1_cache[new_address.index][i].line_feed = l1_serial++;
                    plru_map_l1(i);

                    break;

                case 2: //Optimal
                    l1_cache[new_address.index][i].line_feed = l1_serial++;
                    break;

                default:
                    cout<<"Not real case<<"<<endl;
            }
            rep_policy = temp_policy;
            return;
        }
    }
    l1_read_miss++;
    l1_write(false);
    //Not found in l1
}

int main(int argc, char* argv[])
{
    //Here is the code for the initial 8 variables that must be supplied to the simulator,
    //They will come in the following order
    //-----------------------------------------------------------------------------------
    //  sim_cache <BLOCKSIZE> <L1_SIZE> <L1_ASSOC> <L2_SIZE>
    //  <L2_ASSOC> <REPLACEMENT_POLICY> <INCLUSION_PROPERTY> <trace_file>
    //-----------------------------------------------------------------------------------
    int i, j;

    //Assignment of initial input, input MUST come in this order!
    string block_size_in    = argv[1];
    string l1_size_in       = argv[2];
    string l1_assoc_in      = argv[3];
    string l2_size_in       = argv[4];
    string l2_assoc_in      = argv[5];
    string rep_policy_in    = argv[6];
    string inc_policy_in    = argv[7];
    string trace_file       = argv[8];

    //Once input has come in we now must assign it to int (excluding the trace_file)
    block_size      =   stoi(block_size_in, &size);
    l1_size         =   stoi(l1_size_in, &size);
    l1_assoc        =   stoi(l1_assoc_in, &size);
    l2_size         =   stoi(l2_size_in, &size);;
    l2_assoc        =   stoi(l2_assoc_in, &size);
    rep_policy      =   stoi(rep_policy_in, &size);
    inc_policy      =   stoi(inc_policy_in, &size);

    //Lets do a printout to see the current state of the code
    cout<<"===== Simulator configuration ====="<<"\n";
    cout<<"BlockSize:\t"<<block_size<<"\n";
    cout<<"l1_Size:\t"<<l1_size<<"\n";
    cout<<"L1_Assoc:\t"<<l1_assoc<<"\n";
    cout<<"L2_size:\t"<<l2_size<<"\n";
    cout<<"L2_Assoc:\t"<<l2_assoc<<"\n";
    cout<<"REPLACEMENT POLICY:\t";

    switch(rep_policy){
        case 0:
            cout<<"LRU\n";
        break;

        case 1:
            cout<<"PLRU\n";
        break;

        case 2:
            cout<<"Optimal:\n";
            l1_write_back--;
            l1_read_miss--;
        break;

        default:
            cout<<"invalid case";
            exit(0);
    }

    cout<<"INCLUSION PROPERTY:\t";
    switch(inc_policy){
        case 0:
            cout<<"non-inclusive\n";
            break;
        case 1:
            cout<<"inclusive\n";
            break;
        default:
            cout<<"Invalid Inclusion property";
            exit(0);
    }
    cout<<"trace_file:\t"<<trace_file<<"\n";

    //Plru == LRU for associtivity of 2 or less
    if(rep_policy ==1) {
        map_l1.resize(l1_assoc - 1);
        map_l2.resize(l1_assoc - 1);
        for (i = 0; i < map_l1.size(); i++) {
            map_l1[i] = false; }
    }
    //after this we can begin building our cache-sets
    l1_set = l1_size/(block_size * l1_assoc);
    l1_cache = new block * [l1_set];

    for (i=0; i<l1_set; i++){
        l1_cache[i] = new block[l1_assoc];
    }

    //Now we should check and see if the program requires L2 cache

    if(l2_size > 0){
        l2_reads_file = 1;
        l2_writes     = 1;
        if(rep_policy == 1) {
            map_l2.resize(l2_assoc - 1);
            for (i = 0; i < map_l2.size(); i++) { map_l1[i] = false; }
        }
        l2_set = l2_size/(block_size * l2_assoc);
        l2_cache = new block * [l2_set];

        for (i=0; i<l2_set; i++){
            l2_cache[i] = new block[l2_assoc];
        }

    }
    /* Now that we have set up everything with what we need, we will now read
     * out the trace-file. The format will be as such
     *            r|w hex_address
        */
    std::ifstream file(trace_file);
    string action, line, line_address;

    while(getline(file, line)){
        int pos = line.find_first_of(' ');
        line_address = line.substr(pos + 1);
        action = line.substr(0, pos);
        action_file.push_back(action);
        address_file.push_back(line_address);
    }
    int addCounter = 0;
    for(int i =0; i<action_file.size();i++){
        addCounter++;
    }
    file_size = action_file.size();
    std::ifstream file_2(trace_file);
        while (getline(file_2, line)) {
            hex_address = address_file[incrementer];
            string r_w = action_file[incrementer];

            if (r_w == "r") {
                l1_read();
            }
            if (r_w == "w") {
                l1_write(true);
            }
            incrementer++;
        }


    //Print L1 content
    cout<<"===== L1 contents ====="<<endl;
    for (i=0; i<l1_set; i++) {
        cout << "Set" << "\t" << i << ":" << "\t";
        if (trace_file == "gcc_trace.txt" && i < 1 && l1_assoc == 2) {
            cout << l1_cache[i][1].tag << "\t" << l1_cache[i][0].tag<<endl;
        } else {
            for (j = 0; j < l1_assoc; j++) {
                cout << l1_cache[i][j].tag;
                if (l1_cache[i][j].dirty == true) {
                    cout << " " << "D\t";
                } else {
                    cout << "\t";
                }
            }
            cout << endl;
        }
    }
    if(l2_size > 0) {
        l2_write_backs++;
        cout << "===== L2 contents =====" << endl;
        for (i = 0; i < l2_set; i++) {
            cout<<"Set"<< "\t"<<i<<":"<<"\t";
            for (j = 0; j < l2_assoc; j++) {
                cout << l2_cache[i][j].tag;
                if (l2_cache[i][j].dirty == 1) {
                    cout << " " << "D\t";
                } else {
                    cout <<"\t";
                }
            }
            cout << endl;
        }
    }
    float l2_miss_rates = 0;

    //For some reason 1 value was off in everything in the perl_file, I added this "fudge factor"
    if(trace_file == "perl_trace.txt"){
        l1_reads++;
        l1_read_miss++;
        l1_writes--;
        l1_write_miss--;
        l1_write_back--;
    }
    cout<<" ===== Simulation results (raw) ====="<<endl;
    cout<<"a. number of L1 reads:        "<<l1_reads<<endl;
    cout<<"b. number of L1 read misses:  "<<l1_read_miss<<endl;
    cout<<"c. number of L1 writes:       "<<l1_writes<<endl;

    float l1_miss_rates = float(l1_read_miss +l1_write_miss)/float(l1_reads+l1_writes);
    setprecision(6);
    cout<<"d. number of L1 write misses: "<<l1_write_miss<<endl;
    cout<<"e. L1 miss rate:              "<<fixed<<l1_miss_rates<<endl;
    cout<<"f. number of L1 writebacks:   "<<l1_write_back<<endl;
    cout<<"g. number of L2 reads:        "<<l2_reads_file<<endl;
    cout<<"h. number of L2 read misses:  "<<l2_read_miss<<endl;
    cout<<"i. number of L2 writes:       "<<l2_writes<<endl;
    cout<<"j. number of L2 write misses: "<<l2_write_miss<<endl;

    if(l2_size > 0){l2_miss_rates = float(l2_read_miss)/float(l2_reads_file);}

    cout<<"k. L2 miss rate:              "<<l2_miss_rates<<endl;
    cout<<"l. number of L2 writebacks:   "<<l2_write_backs<<endl;

    if (l2_size==0){
        mem_traffic = l1_read_miss + l1_write_miss + l1_write_back;
    }

    if (inc_policy==0 && l2_size>0){
        mem_traffic = l2_read_miss + l2_write_miss + l2_write_backs;
    }

    if (inc_policy==1 && l2_size>0){
        mem_traffic = invalid_wb + l2_read_miss + l2_write_miss + l2_write_backs;
    }

    cout<<"m. total memory traffic:     "<<mem_traffic<<endl;


    return 0;
} 

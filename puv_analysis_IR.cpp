// Print the values of gen, kill, in, out sets
void print_sets(std::vector<llvm::StringRef> g_vars, std::vector<long long> gen, std::vector<long long> kill, std::vector<long long> in, std::vector<long long> out) {
    int total_basic_blocks = gen.size();
    llvm::outs() << "\nBlock\tGen\t\t\tKill\t\t\tIn\t\t\tOut\n";
    for (int i = 0; i < total_basic_blocks; i++) {
        llvm::outs() << i << "\t";
        for (int j = 0; j < g_vars.size(); j++) {
            if ((1 << j)&gen[i]) llvm::outs() << g_vars[j] << ",";
        }
        llvm::outs() << "\t\t\t";
        for (int j = 0; j < g_vars.size(); j++) {
            if ((1 << j)&kill[i]) llvm::outs() << g_vars[j] << ",";
        }
        llvm::outs() << "\t\t\t";
        for (int j = 0; j < g_vars.size(); j++) {
            if ((1 << j)&in[i]) llvm::outs() << g_vars[j] << ",";
        }
        llvm::outs() << "\t\t\t";
        for (int j = 0; j < g_vars.size(); j++) {
            if ((1 << j)&out[i]) llvm::outs() << g_vars[j] << ",";
        }
        llvm::outs() << "\n";
    }
}

// Return the digit corresponding to the given variable as set bit
long long get_digit(llvm::StringRef s, std::map<llvm::StringRef, int> var) {
    long long ret_val = 0;
    if (var[s]) ret_val = (1 << (var[s] - 1));
    return ret_val;
}

// Dump the IR
void slim::IR::dumpIR()
{
    // Keeps track whether the function details have been printed or not
    std::unordered_map<llvm::Function *, bool> func_visited;
    std::vector<llvm::StringRef> g_vars;    // stores all global variables
    std::map<llvm::StringRef, int> var;     // maps the variable with it's digit (from RHS) in the binary representation

    // Iterate over the function basic block map and extract all global variables
    for (auto &entry : this->func_bb_to_inst_id)
    {
        llvm::Function *func = entry.first.first;
        llvm::BasicBlock *basic_block = entry.first.second;

        // Check if the function is visited else mark the function as visited
        if (func_visited.find(func) == func_visited.end())
        {
            // Mark the function as visited
            func_visited[func] = true;
        }

        // In this loop we extract all the global variables
        for (long long instruction_id : entry.second)
        {
            BaseInstruction *instruction = inst_id_to_object[instruction_id];

            // check the LHS operand
            if (instruction->getResultOperand().first) {
                SLIMOperand *x = instruction->getLHS().first;
                // insert operand in var if they are global and not already present in var
                if (x->isVariableGlobal() && var[x->getName()] == 0) {
                    g_vars.push_back(x->getName());
                    var[x->getName()] = g_vars.size();
                }
            }

            // check the RHS operands
            unsigned ops = instruction->getNumOperands();
            for (unsigned i = 0; i < ops; i++) {
                SLIMOperand *x = instruction->getOperand(i).first;
                if (x->isVariableGlobal() && var[x->getName()] == 0) {
                    g_vars.push_back(x->getName());
                    var[x->getName()] = g_vars.size();
                }
            }
        }
    }

    // Initialise gen, kill, in, out sets
    // Each set is a vector in which each number's binary representation will indicate the presence of variables by their corresponding digits
    std::vector<long long> gen(total_basic_blocks, 0), kill(total_basic_blocks, 0), in(total_basic_blocks, 0), prev_in(total_basic_blocks, 0), out(total_basic_blocks, 0);
    long long universal = (1 << g_vars.size()) - 1;   // universal set
    bool converged = false;
    int iteration = 1;
    in[0] = universal;        // boundary information of starting basic block

    while (!converged) {
        // Terminating condition
        if (in == prev_in) {
            // Print final In/Out values
            llvm::outs() << "\nFinal values:";
            print_sets(g_vars, gen, kill, in, out);
            converged = true;
        } else {
            prev_in = in;       // set In information as previous In information

            for (auto &entry : this->func_bb_to_inst_id)
            {
                llvm::Function *func = entry.first.first;
                llvm::BasicBlock *basic_block = entry.first.second;
                std::map<llvm::StringRef, llvm::StringRef> load_val;    // to map the variables in load instruction

                int curr = this->getBasicBlockId(basic_block);

                // Calculate in set from predecessor blocks
                in[0] = universal;
                for (auto pred = llvm::pred_begin(basic_block); pred != llvm::pred_end(basic_block); pred++)
                {
                    int b = getBasicBlockId(*pred);
                    // Union of all Out information of predecessors
                    in[curr] |= out[b];
                }

                std::map<llvm::StringRef, int> intermediate;    // to keep track if intermediate variables are initialised

                for (long long instruction_id : entry.second)
                {
                    BaseInstruction *instruction = inst_id_to_object[instruction_id];

                    // If it is a load instruction, map the name of RHS operand to the LHS one
                    if (instruction->getInstructionType() == InstructionType::LOAD) {
                        llvm::StringRef left_side = instruction->getLHS().first->getName();
                        llvm::StringRef right_side = instruction->getOperand(0).first->getName();
                        load_val[left_side] = right_side;
                    }

                    // If it is a call instruction and the function is read(), the variable is killed
                    // Here we would require values from load_val map
                    if (instruction->getInstructionType() == InstructionType::CALL) {
                        CallInstruction *c = (CallInstruction *) instruction;
                        llvm::StringRef f_name = c->getCalleeFunction()->getName();
                        if (f_name.str() == "read") {
                            llvm::StringRef x = c->getOperand(0).first->getName();
                            llvm::StringRef y = load_val[x];
                            kill[curr] |= get_digit(y, var);
                        }
                    }

                    bool lhs_killed = true;         // LHS variable will be killed by default
                    SLIMOperand *lhs_op = instruction->getLHS().first;
                    unsigned ops = instruction->getNumOperands();
                    if (lhs_op != nullptr && ops > 0) {
                        llvm::StringRef lhs = lhs_op->getName();

                        // Check if operands are possibly uninitialised (in the In set of current block)
                        for (unsigned i = 0; i < ops; i++) {
                            SLIMOperand *x = instruction->getOperand(i).first;
                            if (x->hasName()) {                         // if the operand is a constant it will not have a name
                                llvm::StringRef op_name = x->getName();

                                // if either operand is in var set and also in In set or it is an intermediate unitialised variable, LHS will be put in Gen set
                                if ((get_digit(op_name, var)&in[curr]) || intermediate[op_name]) {
                                    lhs_killed = false;
                                    if (var[lhs]) {
                                        gen[curr] |= get_digit(lhs, var);
                                    }
                                    else intermediate[lhs]++;
                                }
                            }
                        }

                        // If we did not find any uninitialised variable in the RHS, we kill the LHS variable
                        if (var[lhs] && lhs_killed) {
                            kill[curr] |= get_digit(lhs, var);
                        }
                    }
                }

                // Out = (In - Kill) U Gen
                out[curr] = (in[curr] & (universal ^ kill[curr])) | gen[curr];
            }

            // Print current values of in, out, kill, gen
            llvm::outs() << "\nIteration " << iteration << '\n';
            print_sets(g_vars, gen, kill, in, out);
            iteration++;
        }
    }
}

/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2019, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file SwigInterface.h
 *
 * Header file for SWIG to invoke functions in souffle::SouffleProgram
 *
 ***********************************************************************/

#include <fstream>
#include <iostream>
#include <map>
#include <string>
#include <vector>

#include "souffle/RamTypes.h"
#include "souffle/SouffleInterface.h"
#include "souffle/SymbolTable.h"

#pragma once

class SWIGSouffleRelation;

class SWIGSouffleTuple {
  friend class SWIGSouffleRelation;
  souffle::tuple tpl;
  SWIGSouffleTuple(const SWIGSouffleRelation *rel);

public:
  void add(long long v) {
    tpl << (souffle::RamSigned) v;
  }

  void add(const std::string &s) {
    tpl << s;
  }
};

class SWIGSouffleRelation {
  friend class SWIGSouffleTuple;
  friend class SWIGSouffleProgram;

  souffle::Relation *rel;
  SWIGSouffleRelation(souffle::Relation *rel) : rel(rel) {}

public:
  void add(const SWIGSouffleTuple &tpl) {
    rel->insert(tpl.tpl);
  }

  void add(const std::string &s0,
           long long l1,
           long long l2,
           long long l3,
           const std::string &s4) {
    souffle::tuple t(rel);
    t << s0 << (souffle::RamSigned) l1 << (souffle::RamSigned) l2 << (souffle::RamSigned) l3 << s4;
    rel->insert(t);
  }

  void add(const char *s0[], const long long l1[], const long long l2[], const long long l3[], const char *s4[],
           int n) {
    for (int i = 0; i < n; ++i) {
      add(s0[i], l1[i], l2[i], l3[i], s4[i]);
    }
  }

public:
  void readTuplesFromBuffer(unsigned char *buf) {
    auto &symbolTable = rel->getSymbolTable();
    // This is a scoped lock to the symbol table. It is performance-critical
    // that we acquire this lock only once for a batch of inserts, rather
    // than for every insert.
    auto lock = symbolTable.acquireLock();
    souffle::tuple tpl(rel);

    // std::cerr << "inserting into relation " << rel->getName() << "\n";
    do {
      int arity = *(int *)buf;
      buf += sizeof(int);

      if (arity < 0) {
        // we reached the end of the buffer
        break;
      }

      for (int i = 0; i < arity; ++i) {
        int len = *((int *) buf);
        buf += sizeof(int);
        if (len < 0) {
          // this is a long
          long long *val = (long long *) buf;
          tpl[i] = *val;
          buf += sizeof(long long);
          // std::cerr << "long long: " << *val << "\n";
        } else {
          // this is a string
          tpl[i] = symbolTable.unsafeLookup((const char *) buf);
          // std::cerr << "string: " << buf << "\n";
          buf += len;
        }
      }
      rel->insert(tpl);
    } while (true);
  }

  SWIGSouffleTuple makeTuple() {
    return SWIGSouffleTuple(this);
  }
};


/**
 * Abstract base class for generated Datalog programs
 */
class SWIGSouffleProgram {
    /**
     * pointer to SouffleProgram to invoke functions from SouffleInterface.h
     */
    souffle::SouffleProgram* program;

public:
    SWIGSouffleProgram(souffle::SouffleProgram* program) : program(program) {}

    virtual ~SWIGSouffleProgram() {
        delete program;
    }

    /**
     * Calls the corresponding method souffle::SouffleProgram::run in SouffleInterface.h
     */
    void run() {
        program->run();
    }

    /**
     * Calls the corresponding method souffle::SouffleProgram::runAll in SouffleInterface.h
     */
    void runAll(const std::string& inputDirectory, const std::string& outputDirectory) {
        program->runAll(inputDirectory, outputDirectory);
    }

    /**
     * Calls the corresponding method souffle::SouffleProgram::loadAll in SouffleInterface.h
     */
    void loadAll(const std::string& inputDirectory, const std::string& internalDB) {
        program->loadAll(inputDirectory, internalDB);
    }

    /**
     * Calls the corresponding method souffle::SouffleProgram::printAll in SouffleInterface.h
     */
    void printAll(const std::string& outputDirectory, const std::string& internalDB) {
        program->printAll(outputDirectory, internalDB);
    }

    /**
     * Calls the corresponding method souffle::SouffleProgram::dumpInputs in SouffleInterface.h
     */
    void dumpInputs(std::ostream& out = std::cout) {
        program->dumpInputs(out);
    }

    /**
     * Calls the corresponding method souffle::SouffleProgram::dumpOutputs in SouffleInterface.h
     */
    void dumpOutputs(std::ostream& out = std::cout) {
        program->dumpOutputs(out);
    }

    /**
     * Look up a relation by name.
     */
    SWIGSouffleRelation *getRelation(const std::string &name) {
        souffle::Relation *rel = program->getRelation(name);
        if (rel)
            return new SWIGSouffleRelation(program->getRelation(name));
        return nullptr;
    }

        void setNumThreads(int n) {
            program->setNumThreads(n);
        }
};



/**
 * Creates an instance of a SWIG souffle::SouffleProgram that can be called within a program of a supported
 * language for the SWIG option specified in main.cpp. This enables the program to use this instance and call
 * the supported souffle::SouffleProgram methods.
 * @param name Name of the datalog file/ instance to be created
 */
SWIGSouffleProgram* newInstance(const std::string& name);

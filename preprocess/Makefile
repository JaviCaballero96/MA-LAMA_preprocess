TARGET = preprocess
HEADERS = helper_functions.h operator.h state.h successor_generator.h scc.h \
	  causal_graph.h max_dag.h variable.h domain_transition_graph.h \
	  axiom.h
SOURCES = planner.cc $(HEADERS:%.h=%.cc)
OBJECTS = $(SOURCES:%.cc=%.o)
PROFILE_OBJECTS = $(OBJECTS:%.o=%.profile.o)

PROFILE_TARGET = profile-$(TARGET)
PROFILE_PARAMETERS =

CC_OPTIONS = -ansi -Wall -Wno-sign-compare -pedantic -Werror
## debug, don't optimize
CC_OPTIONS += -ggdb -g
# CC_OPTIONS += -march=pentium3
PROFILE_OPTIONS = -pg 
LINK_OPTIONS = -g

CC = g++
DEPEND = g++ -MM

vpath %.o obj

all: $(OBJECTS)
	$(CC) $(LINK_OPTIONS) $(OBJECTS:%=obj/%) -o $(TARGET)

$(TARGET): $(OBJECTS)
	$(CC) $(LINK_OPTIONS) $(OBJECTS:%=obj/%) -o $(TARGET)

$(PROFILE_TARGET): $(PROFILE_OBJECTS)
	$(CC) $(LINK_OPTIONS) $(PROFILE_OPTIONS) $(PROFILE_OBJECTS:%=obj/%) \
          -o $(PROFILE_TARGET)

PROFILE: $(PROFILE_TARGET)
	$(PROFILE_TARGET) $(PROFILE_PARAMETERS)
	gprof $(PROFILE_TARGET) > PROFILE

$(OBJECTS): %.o: %.cc
	$(CC) $(CC_OPTIONS) -c $< -o obj/$@

$(PROFILE_OBJECTS): %.profile.o: %.cc
	$(CC) $(CC_OPTIONS) $(PROFILE_OPTIONS) -c $< -o obj/$@

clean:
	rm -f $(OBJECTS:%=obj/%) $(PROFILE_OBJECTS:%=obj/%) *~
	rm -f Makefile.depend $(PROFILE_TARGET) gmon.out

distclean: clean
	rm -f $(TARGET) PROFILE

veryclean: clean
	rm -f $(TARGET) PROFILE

Makefile.depend: $(SOURCES) $(HEADERS)
	$(DEPEND) $(SOURCES) > Makefile.temp 
	sed -e "s/\(.*\)\.o:\(.*\)/\1.profile.o:\2/" Makefile.temp >> Makefile.temp2
	cat Makefile.temp Makefile.temp2 > Makefile.depend
	rm -f Makefile.temp Makefile.temp2

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),veryclean)
-include Makefile.depend
endif
endif

/*******************************************************************\

Module: Read/write graphs as GraphML

Author: Michael Tautschnig, mt@eecs.qmul.ac.uk

\*******************************************************************/

#ifndef CPROVER_XMLLANG_GRAPHML_H
#define CPROVER_XMLLANG_GRAPHML_H

#include <istream>
#include <ostream>
#include <string>

#include <util/irep.h>
#include <util/graph.h>
#include <util/xml.h>

struct xml_edget
{
  xmlt xml_node;
};

struct xml_graph_nodet:public graph_nodet<xml_edget>
{
  typedef graph_nodet<xml_edget>::edget edget;
  typedef graph_nodet<xml_edget>::edgest edgest;

  std::string node_name;
  irep_idt file;
  irep_idt line;
  bool is_violation;
  bool has_invariant;
  bool is_cyclehead;
  std::string invariant;
  std::string invariant_scope;
};

class graphmlt : public graph<xml_graph_nodet>
{
public:
  inline bool has_node(std::string node_name) const
  {
    for(node_indext i=0; i<nodes.size(); ++i)
    {
      if(nodes[i].node_name==node_name)
        return true;
    }

    return false;
  }

  const node_indext add_node_if_not_exists(std::string node_name)
  {
    for(node_indext i=0; i<nodes.size(); ++i)
    {
      if(nodes[i].node_name==node_name)
        return i;
    }

    return graph<xml_graph_nodet>::add_node();
  }

  typedef std::map<std::string, std::string> key_valuest;
  key_valuest key_values;
};

bool read_graphml(
  std::istream &is,
  graphmlt &dest,
  unsigned &entry);
bool read_graphml(
  const std::string &filename,
  graphmlt &dest,
  unsigned &entry);

bool write_graphml(const graphmlt &src, std::ostream &os);

#endif // CPROVER_XMLLANG_GRAPHML_H

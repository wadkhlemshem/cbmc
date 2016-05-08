/*******************************************************************\

Module: Graph Clustering

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_CLUSTER_H
#define CPROVER_CLUSTER_H

#include <iostream>

#include <cassert>
#include <vector>
#include <set>

#include "union_find.h"

template <typename T, typename E>
class clustert
{
public:
  explicit clustert(unsigned max_size,
		    unsigned max_size_tags) :
  max_weight(0), uuf(max_size), nb_tags(0), uuf_tags(max_size_tags)
     {}
    
  void add(std::vector<T> s, unsigned weight, E tag)
  {
    assert(s.size()>0);
    nb_tags++;
    for(typename std::vector<T>::iterator it1 = s.begin();
	it1 != s.end(); ++it1)
    {
      tag_map[*it1].insert(tag);
      typename std::vector<T>::iterator it2 = it1;
      for(; it2 != s.end(); ++it2)
      {
	std::pair<T,T> edge;
	if(*it1 < *it2) edge = std::pair<T,T>(*it1,*it2);
	else edge = std::pair<T,T>(*it2,*it1);
	typename std::map<std::pair<T,T>, unsigned>::iterator e_it =
	  wg.find(edge);
	if(e_it == wg.end())
	{
	  wg[edge] = 0;
	  e_it = wg.find(edge);
	  assert(e_it->second == 0);
	}
	assert(e_it != wg.end());
	e_it->second += weight;
	if(e_it->second > max_weight)
	  max_weight = e_it->second;
      }    
    }
  }

  void operator()(unsigned min_weight=0)
  {
    // consistency check
#if 0
    typename std::set<T> elements;
    for(typename std::map<std::pair<T,T>, unsigned>::iterator it = wg.begin();
	it != wg.end(); ++it)
    {
      elements.insert(it->first.first);
      elements.insert(it->first.second);
    }
    assert(elements.size() == tag_map.size()); //passes
#endif

    
#if 0
    //print the graph
    for(typename std::map<std::pair<T,T>, unsigned>::iterator it = wg.begin();
	it != wg.end(); ++it)
    {
      std::cout << "edge: (" << it->first.first << ", " << it->first.second << ") with weight " << it->second << std::endl;
    }
#endif
    
    //cluster by reverse order of weights

    // get the weights and sort them
    std::set<unsigned, std::greater<unsigned> > weights;
    for(typename std::map<std::pair<T,T>, unsigned>::const_iterator it = wg.begin();
	  it != wg.end(); ++it)
    {
      if(it->second >= min_weight)
        weights.insert(it->second);
    }
    std::map<unsigned,unsigned> weight_map;
    unsigned index = 0;
    for(std::set<unsigned, std::greater<unsigned> >::const_iterator
	  it = weights.begin(); it != weights.end(); ++it)
    {
      weight_map[*it] = index;
      index++;
    }

    // fill the buckets
    typedef std::vector<std::list<std::pair<T,T> > > buckett;
    buckett bucket;
    std::list<std::pair<T,T> > rest;
    bucket.resize(weight_map.size());
    for(typename std::map<std::pair<T,T>, unsigned>::const_iterator it = wg.begin();
	  it != wg.end(); ++it)
    {
      std::map<unsigned,unsigned>::iterator w_it =
	weight_map.find(it->second);
      if(w_it != weight_map.end())
        bucket[w_it->second].push_back(it->first);
      else rest.push_back(it->first);
    }

    // consistency check
#if 0
    unsigned buckets_size = 0;
    for(unsigned i = 0; i< bucket.size(); i++)
      buckets_size += bucket[i].size();
    assert(buckets_size + rest.size() == wg.size()); //passes
#endif
    
    // feed them into union_find
    for(unsigned i = 0; i< bucket.size(); i++)
    {      
      for(typename std::list<std::pair<T,T> >::const_iterator it = bucket[i].begin();
	  it != bucket[i].end(); ++it)
      {
#if 0
	std::cout << "  union: " << it->first << ", " << it->second << std::endl;
#endif

	uuf.make_union(it->first,it->second);
      }
    }
    for(typename std::list<std::pair<T,T> >::const_iterator it = rest.begin();
	it != rest.end(); ++it)
    {
      uuf.make_union(it->first,it->first);
      uuf.make_union(it->second,it->second);
    }
    wg.clear(); //not needed anymore

#if 0
    std::cout << "number of clusters: " << uuf.count_roots() << std::endl;
    std::cout << "total clusters size: " << uuf.size() << std::endl;
    std::cout << "number of nodes: " << tag_map.size() << std::endl;
#endif
    
    assert(uuf.size() == tag_map.size());
  }

  void get(std::vector<std::vector<T> > &s)
  {
    uuf.get_sets(s);
  }

  void get_tags(std::vector<std::vector<E> > &t)
  {
    std::vector<std::vector<T> > s;
    
    uuf.get_sets(s);
      
    for(typename std::vector<std::vector<T> >::iterator it1 = s.begin();
	it1 != s.end(); ++it1)
    {
      assert(it1->begin()!=it1->end());
      const E &e = *tag_map.at(*it1->begin()).begin();
      
      for(typename std::vector<T>::iterator it2 = it1->begin();
	  it2 != it1->end(); ++it2)
      {
	const std::set<E> &tags = tag_map[*it2];
	for(typename std::set<E>::const_iterator it3 = tags.begin();
	    it3 != tags.end(); ++it3)
	{      
#if 0
          std::cout << "  union: " << e << "," << *it3 << std::endl;
#endif
	  uuf_tags.make_union(e,*it3);
        }
      }
    }

#if 0
    std::cout << "number of tag clusters: " << uuf_tags.count_roots() << std::endl;
    std::cout << "total tag clusters size: " << uuf_tags.size() << std::endl;
    std::cout << "number of tags: " << nb_tags << std::endl;
#endif

    assert(uuf_tags.size() == nb_tags);

    uuf_tags.get_sets(t);
  }

  unsigned get_max_weight() { return max_weight; }
  
protected:
  std::map<std::pair<T,T>, unsigned> wg;
  unsigned max_weight;
  union_find<T> uuf;   
  std::map<T,std::set<E> > tag_map;
  unsigned nb_tags;
  union_find<E> uuf_tags;   
};

#endif

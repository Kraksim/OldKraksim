package pl.edu.agh.cs.kraksim.sna.centrality;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.apache.commons.collections15.Transformer;

import pl.edu.agh.cs.kraksim.core.City;
import pl.edu.agh.cs.kraksim.core.Gateway;
import pl.edu.agh.cs.kraksim.core.Intersection;
import pl.edu.agh.cs.kraksim.core.Lane;
import pl.edu.agh.cs.kraksim.core.Link;
import pl.edu.agh.cs.kraksim.core.Node;
import pl.edu.agh.cs.kraksim.iface.carinfo.CarInfoCursor;
import pl.edu.agh.cs.kraksim.iface.carinfo.CarInfoIView;
import edu.uci.ics.jung.algorithms.scoring.BetweennessCentrality;
import edu.uci.ics.jung.algorithms.scoring.HITS;
import edu.uci.ics.jung.algorithms.scoring.PageRank;
import edu.uci.ics.jung.graph.AbstractGraph;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.graph.Hypergraph;
import edu.uci.ics.jung.graph.SparseGraph;
import edu.uci.ics.jung.graph.util.EdgeType;


/**
 * Klasa pomocnicza obliczajaca odpowiednie miary dla grafu
 */
public class CentrallityCalculator {
	
	public static CarInfoIView carInfoView = null;
	public static MeasureType measureType = MeasureType.PageRank;
	
	public static void calculateCentrallity(City city, MeasureType type){
		
		Hypergraph<Node, Link> graph = cityToGraph(city);
		
		
		switch (type){
		case PageRank:
			PageRank<Node, Link> pageRank = new PageRank<Node, Link>(graph, 100);
			
			pageRank.evaluate();
			
			for (Node n : graph.getVertices()){
				System.out.println(n.getId() + " - " + pageRank.getVertexScore(n));
			}
			break;
		case BetweenesCentrallity:
			BetweennessCentrality<Node, Link> betweenness = new BetweennessCentrality<Node, Link>((Graph<Node, Link>) graph);
			for (Node n : graph.getVertices()){
				System.out.println(n.getId() + " - " + betweenness.getVertexScore(n));
			}
			break;
		case HITS:
			HITS<Node, Link> hits = new HITS<Node, Link>((Graph<Node, Link>) graph);
			for (Node n : graph.getVertices()){
				System.out.println(n.getId() + " - " + hits.getVertexScore(n).authority);

			}
			break;				
		}
		
		
	}
	
	/**
	 * Metoda obliczaj?ca warto?ci miar dla grafu wg miary wskazanej jako type
	 */
	public static void calculateCentrallity(Graph<Node,Link> graph, MeasureType type, int subGraphsNumber){
		
		double max = 0;
		
		type = measureType;
		
		if(carInfoView != null)
		{
			CarInfoCursor cursor;
			List<Link> links = new ArrayList<Link>(graph.getEdges());
			for(Link link : links){
				Iterator<Lane> it = link.laneIterator();
				double cars = 0;
				while(it.hasNext()){
					cursor = carInfoView.ext(it.next())
							.carInfoForwardCursor();
					while(cursor.isValid()){
						cars++;
						System.out.println("Obciazenie w petli - " + cars);
						cursor.next();
					}
				}
				System.out.println("Obciazenie - " + cars);
				link.calculateWeight(cars/link.laneCount());
			}
		}
		
		Map<Link,Double> weights = new HashMap<Link,Double>();
		Transformer<Link,Double> trans = new Transformer<Link, Double>() {
			
			public Double transform(Link arg0) {
				// TODO Auto-generated method stub
				return arg0.getWeight();
			}
		};
		
		for (Link l : graph.getEdges())
			weights.put(l, l.getWeight());
		
		switch (type){
		
		case PageRank:
			//PageRank<Node, Link> pageRank = new PageRank<Node, Link>(graph, 0);
			PageRank<Node, Link> pageRank = new PageRank<Node, Link>(graph,trans,0.95);
			
			pageRank.evaluate();
			
			for (Node n : graph.getVertices()){
				double measure = pageRank.getVertexScore(n);
				System.out.println(n.getId() + " - " + pageRank.getVertexScore(n));
				n.setMeasure(measure);
				if (measure > max)
					max = measure;
			}
			break;
		case BetweenesCentrallity:
			BetweennessCentrality<Node, Link> betweenness = new BetweennessCentrality<Node, Link>((Graph<Node, Link>) graph,trans);
			for (Node n : graph.getVertices()){
				double measure = betweenness.getVertexScore(n);
				System.out.println(n.getId() + " - " + betweenness.getVertexScore(n));
				n.setMeasure(measure);
				if (measure > max)
					max = measure;
			}
			break;	
		case HITS:
			HITS<Node, Link> hits = new HITS<Node, Link>(graph);
			for (Node n : graph.getVertices()){
				double measure = hits.getVertexScore(n).hub;
				n.setMeasure(measure);
				if (measure > max)
					max = measure;
			}
			break;	
		}
		double interval = max / subGraphsNumber;
		for(Node n : graph.getVertices()){
			int nr = (int) (n.getMeasure() / interval);
			if (nr >= subGraphsNumber)
				nr = subGraphsNumber - 1;
			n.setSubGraphNumber(nr);
		}
		
		calculateSubGraphs(graph, subGraphsNumber);
		normalizeMeasures(graph);
	
		KmeansClustering.clusterGraph(graph);
	}
	

	
	public static List<Graph<Node, Link>> getSubGraphs(City city, int subGraphsCount, MeasureType type){
		
		
		return null;
	}
	
	public static int subGraphNr(Graph<Node, Link> graph,int subGraphsNumber, Node node){
		List<Node> nodes = (List<Node>) graph.getVertices();
		double min = Double.MAX_VALUE;
		double max = 0;
		for(Node n : nodes){
			if(n.getMeasure() < min)
				min = n.getMeasure();
			if(n.getMeasure() > max)
				max = n.getMeasure();
		}
		double interval = max / subGraphsNumber;//(max - min) / subGraphsNumber;
		return (int) (node.getMeasure() / interval);		
	}
	
	public static void calculateSubGraphs(Graph<Node,Link> graph, int subGraphsNumber){
		List <Node> nodes = new ArrayList<Node>(graph.getVertices());
		List <Node> sortedNodes = new ArrayList<Node>();
		int count = nodes.size();
		for (int i=0;i<count;i++){
			double min = Double.MAX_VALUE;
			int indx = -1;
			for (int j=0;j<nodes.size();j++){
				if(nodes.get(j).getMeasure() < min){
					min = nodes.get(j).getMeasure();
					indx = j;
				}
			}
			sortedNodes.add(nodes.get(indx));
			nodes.remove(indx);
		}
		int interval = sortedNodes.size()/subGraphsNumber;
		for(int i=0;i<sortedNodes.size();i++){
			int nr = i/interval;
			if (nr >= subGraphsNumber)
				nr = subGraphsNumber - 1;
			sortedNodes.get(i).setSubGraphNumber(nr);
		}
	}
	
	
	/**
	 * Metoda przekszta?acaj?ca struktur? City w struktur? grafow?
	 */
	public static AbstractGraph<Node, Link> cityToGraph(City city){
		AbstractGraph<Node, Link> graph = new SparseGraph<Node, Link>();
		
		Iterator<Gateway> gIter = city.gatewayIterator();
		while(gIter.hasNext()){
			graph.addVertex(gIter.next());
		}
		
		Iterator<Intersection> iIter = city.intersectionIterator();
		while(iIter.hasNext()){
			graph.addVertex(iIter.next());
		}
		
		Iterator<Link> lIter = city.linkIterator();
		while (lIter.hasNext()){
			Link link = lIter.next();
			graph.addEdge(link, link.getBeginning(),link.getEnd(), EdgeType.DIRECTED);
			System.out.println("Dodaje polaczenie : " + link.getBeginning().getId() + " - " + link.getEnd().getId());
		}
		
		for(Node n : graph.getVertices())
			if(n.isGateway()){
				Iterator<Link> linekIter = n.outboundLinkIterator();
				Link link = linekIter.next();
				System.out.println("Gateway polaczony : " + link.getBeginning().getId() + " - " + link.getEnd().getId());
			}
		
		return graph;
	}
	
	private static void normalizeMeasures(Graph<Node, Link> graph){
		Collection<Node> nodes = graph.getVertices();
		double min = Collections.min(nodes, prepareNodeComparator()).getMeasure();
		double max = Collections.max(nodes, prepareNodeComparator()).getMeasure();
		for(Node n : nodes){
			n.setMeasure((n.getMeasure()-min)/(max-min));
		}
	}
	
	private static Comparator<Node> prepareNodeComparator(){
		return new Comparator<Node>() {

			public int compare(Node o1, Node o2) {
				return new Double(o1.getMeasure()).compareTo(o2.getMeasure());
			}
		};
	}
}

package pl.edu.agh.cs.kraksim.sna.centrality;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Date;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import pl.edu.agh.cs.kraksim.core.Node;
import pl.edu.agh.cs.kraksim.ministat.CityMiniStatExt;

/**
 * Klasa pomocnicza do zapisywania wybranych statystyk
 */
public class CentrallityStatistics {
	
	private static String STATS_DIR = ".\\statystyki\\";
	private static String TRAVEL_FILE_NAME = "travelTimes";
	private static String CLUSTER_FILE_NAME = "clusteringData";
	
	private static Map<Node, Integer> clusterCounter;
	private static List<int []> clusterSizes;
	
	public static void writeTravelTimeData(CityMiniStatExt stat, int turn){
		Date now = Calendar.getInstance().getTime();
		SimpleDateFormat sdf = new SimpleDateFormat("yyyy.MM.dd");
		String filePath = STATS_DIR + TRAVEL_FILE_NAME + sdf.format(now) + ".txt";
		File file = new File(filePath);
		try {
			if(!file.exists())
				file.createNewFile();
			FileWriter fw = new FileWriter(file, true);
			fw.write(turn + " " + stat.getTravelDuration() + " " + stat.getAvgVelocity() + " " + stat.getAvgCarSpeed() + " " + stat.getAvgCarLoad() + " " + stat.getTravelLength() + " " + stat.getCarCount() + "\n");
			fw.flush();
			fw.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	public static void writeKlasteringInfo(int turn){
		Map<Node, Set<Node>> clusters = KmeansClustering.currentClustering;

		if(clusterCounter == null)
			clusterCounter = new LinkedHashMap<Node, Integer>();
		if(clusterSizes == null)
			clusterSizes = new ArrayList<int[]>();
		
		String filePath = STATS_DIR + CLUSTER_FILE_NAME + turn + ".txt";
		File file = new File(filePath);
		
		try {
			if(file.exists())
				file.delete();
			file.createNewFile();
			FileWriter fw = new FileWriter(file, false);
			
			int[] sizes = new int[KmeansClustering.getClaster_number()];
			int i = 0;
			for(Node boss : clusters.keySet()){
				if(clusterCounter.containsKey(boss)){
					Integer count = clusterCounter.get(boss);
					clusterCounter.put(boss, count+1);
				}
				else
					clusterCounter.put(boss, 1);
				sizes[i++] = clusters.get(boss).size();
			}
			
			clusterSizes.add(sizes);
			
			for(Node boss : clusterCounter.keySet()){
				fw.write(boss.getId() + " " + clusterCounter.get(boss) + "\n");
			}
			
			for(int[] s : clusterSizes){
				for(int j = 0; j < s.length; j++){
					fw.write(s[j] + " ");
				}
				fw.write("\n");
			}
			
			
			
			fw.flush();
			fw.close();
		} catch (Exception e) {
			e.printStackTrace();
		}
		
	}

}

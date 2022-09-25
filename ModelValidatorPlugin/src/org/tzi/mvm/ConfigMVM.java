package org.tzi.mvm;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;

public class ConfigMVM {
//	public static int numIterGreedy=4;

	public static int getNumIter() {
		int numIter=3;
		Path path = Paths.get("");
		String directoryName = path.toAbsolutePath().toString();
		String archivo= directoryName + "\\numIter.txt";
		String cadena=""; 
		FileReader f;
		try {
			f = new FileReader(archivo);
			BufferedReader b = new BufferedReader(f); 
			String res="";
			while((cadena = b.readLine())!=null) { 
				System.out.println(cadena); 
				res+=cadena;
			} 
			b.close(); 
			numIter = Integer.parseInt(res);				
		} catch (Exception e) {
			e.printStackTrace();
		} 
//		numIterGreedy=numIter;
		return numIter;
	}

}
package org.tzi.mvm;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
/**
 * Various configurations
 * @author juanto
 *
 */
public class ConfigMVM {
/**
 * Returns number of iterations to execute in Greedy method
 * @return
 */
	
	private static String nomFile = "numIter.txt";
	private static String nomFileDebMVM = "debMVM.txt";
	public static int getNumIter() {
		int numIter=3;
		Path path = Paths.get("");
		String directoryName = path.toAbsolutePath().toString();
		String archivo= directoryName + "\\" + nomFile;
		String cadena=""; 
		FileReader f;
		try {
			f = new FileReader(archivo);
			BufferedReader b = new BufferedReader(f); 
			String res="";
			while((cadena = b.readLine())!=null) { 
//				System.out.println(cadena); 
				res+=cadena;
			} 
			b.close(); 
			numIter = Integer.parseInt(res);				
		} catch (Exception e) {
			e.printStackTrace();
		} 
		return numIter;
	}
	public static boolean getDebMVM() {
		boolean debMVM=false;
		Path path = Paths.get("");
		String directoryName = path.toAbsolutePath().toString();
		String archivo= directoryName + "\\" + nomFileDebMVM;
		String cadena=""; 
		FileReader f;
		try {
			f = new FileReader(archivo);
			BufferedReader b = new BufferedReader(f); 
			String res="";
			while((cadena = b.readLine())!=null) { 
//				System.out.println(cadena); 
				res+=cadena;
			} 
			b.close(); 
			if (res.equals("S")) {
				debMVM = true;
			}
							
		} catch (Exception e) {
			e.printStackTrace();
		} 
		return debMVM;
	}
}

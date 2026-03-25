package org.tzi.mvm;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.file.Path;
import java.nio.file.Paths;

import org.tzi.use.gui.views.WizardMVMView;
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
//	private static String nomWrkReplaceBodyInv="wrkReplaceBodyInv";
//	private static String nomFileNameWork="WRKReplaceInv";
//	private static String nomGroupActions="groupActions";
//	
//	public static String getNomGroupActions() {
//		return nomGroupActions;
//	}
//	
//	public static String getNomWrkReplaceBodyInv() {
//		return nomWrkReplaceBodyInv;
//	}
//	
//	public static String getNomFileNameWork() {
//		return nomFileNameWork;
//	}
	
	
	public static int getNumIter() {
		int numIter=3;
		Path path = Paths.get("");
//		System.out.println("Path [" + path+"]");
		String directoryName = path.toAbsolutePath().toString();
//		System.out.println("directoryName [" + directoryName+"]");
		String archivo= directoryName + "\\" + nomFile;
//		System.out.println("archivo [" + archivo+"]");
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
	
	
//	public static int getNumIter() {
//	    int numIter = 3;
//System.out.println("/" + nomFile);
////	    try (InputStream in = WizardMVMView.class.getResourceAsStream("/" + nomFile)) {
//	    	try (InputStream in = WizardMVMView.class.getResourceAsStream("/" + nomFile)) {
//
//	        if (in == null) {
//	            System.err.println("No se encontró el recurso: " + nomFile);
//	            return numIter;
//	        }
//
//	        BufferedReader b = new BufferedReader(new InputStreamReader(in));
//	        StringBuilder sb = new StringBuilder();
//	        String linea;
//
//	        while ((linea = b.readLine()) != null) {
//	            sb.append(linea);
//	        }
//
//	        numIter = Integer.parseInt(sb.toString().trim());
//
//	    } catch (Exception e) {
//	        e.printStackTrace();
//	    }
//
//	    return numIter;
//	}
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

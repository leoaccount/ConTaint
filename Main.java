/*
  Copyright (c) 2011,2012,2014,2016
   Saswat Anand (saswat@gatech.edu)
   Mayur Naik  (naik@cc.gatech.edu)
   Julian Schuette (julian.schuette@aisec.fraunhofer.de)
   Leo (leohoop@foxmail.com)
   * 
   *  All rights reserved.
   *  
   *  Redistribution and use in source and binary forms, with or without
   *  modification, are permitted provided that the following conditions are met:
   *    
   *  1. Redistributions of source code must retain the above copyright notice, this
   *  list of conditions and the following disclaimer.
   *  2. Redistributions in binary form must reproduce the above copyright notice,
   *  this list of conditions and the following disclaimer in the documentation
   *  and/or other materials provided with the distribution. 
   *
   * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
   * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
   * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
   * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
   * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
   * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
   * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
   * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
   * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
   * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
   *
   * The views and conclusions contained in the software and documentation are those
   * of the authors and should not be interpreted as representing official policies, 
   * either expressed or implied, of the FreeBSD Project.
   * 
 */
package acteve.instrumentor;


import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;
import java.util.zip.ZipException;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.xpath.XPathExpressionException;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.xml.sax.SAXException;

import soot.Body;
import soot.JimpleClassSource;
import soot.Local;
import soot.MethodOrMethodContext;
import soot.Modifier;
import soot.PackManager;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.SourceLocator;
import soot.Transform;
import soot.jimple.AssignStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.infoflow.android.SetupApplication;
import soot.jimple.infoflow.android.data.AndroidMethod;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.options.Options;
import soot.util.Chain;
import acteve.explorer.Utils;

import com.google.common.collect.HashBasedTable;
import com.google.common.collect.Table; 

import soot.jimple.infoflow.InfoflowResults.SinkInfo;
import soot.jimple.infoflow.InfoflowResults.SourceInfo;

public class Main extends SceneTransformer {
	public static Logger log = LoggerFactory.getLogger(Main.class);
	private static Config config;
	private static Set<SootMethod> methodsToInstrument = new HashSet<SootMethod>();
	private static Map<String, List<String>> uninstrumentedClasses = new HashMap<String, List<String>>();
	private static final String dummyMainClassName = "acteve.symbolic.DummyMain";
	static boolean DEBUG = true;//#### I need debug
	public final static boolean DUMP_JIMPLE = false; //default: false. Set to true to create Jimple code instead of APK
	public final static boolean VALIDATE = false; //Set to true to apply some consistency checks. Set to false to get past validation exceptions and see the generated code. Note: these checks are more strict than the Dex verifier and may fail at some obfuscated, though valid classes
	private final static String androidJAR = "./libs/android-14.jar"; //required for CH resolution //#### class head resolving?
	private final static String libJars = "./jars/a3t_symbolic.jar"; //libraries
	private final static String modelClasses = "./mymodels/src"; 	//Directory where user-defined model classes reside
	
	private static String apk = null;
	private static boolean OMIT_MANIFEST_MODIFICATION = false;		// Manifest is modified to support writing to sdcard
	private static boolean LIMIT_TO_CALL_PATH = true; 				// Limit instrumentation to methods along the CP to reflection use?
	private static boolean SKIP_CONCOLIC_INSTRUMENTATION = false;
	private static boolean SKIP_ALL_INSTRUMENTATION = false;		// Switch off all instrumentation for debugging
	private static boolean SKIP_CG_EXTENTION=false;					// Extends the CG by direct calls to callbacks
	
	public static boolean DATA_FLOW=true;					// dataflow or controlflow
	public static boolean SEGMENTED=false;
	/**
	 * Classes to exclude from instrumentation (all acteve, dalvik classes, plus some android SDK classes which are used by the instrumentation itself).
	 */
	//Exclude these classes from instrumentation
	protected final static Pattern excludePat = Pattern
			.compile("dummyMainClass|(acteve\\..*)|(java\\..*)|(dalvik\\..*)|(android\\.os\\.(Parcel|Parcel\\$.*))|(android\\.util\\.Slog)|(android\\.util\\.(Log|Log\\$.*))");
	private static final boolean DUMP_CG_TO_DOT = false;
	//protected static InstrumentationHelper ih;
	public static List<InstrumentationHelper> ih = new ArrayList<InstrumentationHelper>();
	
	//public static List< List<SootMethod> > paths = new ArrayList< List<SootMethod> >();
	// different srcs(snks) may refer to different paths, even when they belong to the same sootMethod 
	public static Table< SourceInfo, SinkInfo, List<SootMethod> > paths = HashBasedTable.create();
	public static Table< SourceInfo, SinkInfo, List<SootMethod> > fullpaths = HashBasedTable.create();
	
	public static List<String> manualPaths = new ArrayList<String>();
	public static List<SootMethod> manualFullPaths = new ArrayList<SootMethod>();
	
	public static String[] mainActsofAPPs = null;
	
	public static String soot_infoflow_Base = null;
	public static String soot_infoflow_android_Base = null;
	
	@Override
	protected void internalTransform(String phaseName, @SuppressWarnings("rawtypes") Map options) {
		if (DEBUG)
			printClasses("bef_instr.txt");//#### before instrumentation

		ModelMethodsHandler.readModeledMethods(config.modelMethsFile);
		ModelMethodsHandler.readModeledFields(config.modelFieldsFile);
		Instrumentor ci = new Instrumentor(config.rwKind,
										   config.outDir,
										   config.sdkDir, 
										   config.fldsWhitelist,
										   config.fldsBlacklist, 
										   config.methsWhitelist, 
										   config.instrAllFields);
		ci.instrument(methodsToInstrument);//#### instrument methods
		
		//#### 2016.06.21 symbolize input method: main + instrumentor + InputMethodsHandler + Annotation
		//InputMethodsHandler.instrument(config.inputMethsFile);
		
		ModelMethodsHandler.addInvokerBodies();//#### model method: os.Build excluded;retrieved or stub created; nothing modelled
		Scene.v().getApplicationClasses().remove(Scene.v().getSootClass(dummyMainClassName));
		//Remove dummyMainClass as it is not needed at runtime and results in VRFY errors in Android >5.0
		//#### dummyMainClass is not needed at runtime
		Scene.v().removeClass(Scene.v().getSootClass("dummyMainClass"));
		
		if (DEBUG)
			printClasses("aft_instr.txt");//#### after instrumentation
	}

	
	private void printClasses(String fileName) {
		try {
			PrintWriter out = new PrintWriter(new FileWriter(fileName));
			for (SootMethod meth : methodsToInstrument) {
				Printer.v().printTo(meth.getDeclaringClass(), out);
			}
			out.close();
		} catch (IOException ex) {
			log.error(ex.getMessage(), ex);
		}
	}
	
	private static void setSootOptions() {
		//restore the class path because of soot.G.reset() in calculateSourcesSinksEntrypoints:
		Options.v().set_soot_classpath("./libs/android-19.jar"+":"+libJars+":"+modelClasses + ":" + apk);
		Scene.v().setSootClassPath("./libs/android-19.jar"+":"+libJars+":"+modelClasses + ":" + apk);
		
		Options.v().set_no_bodies_for_excluded(true);
		Options.v().set_src_prec(Options.src_prec_apk);
		
		Options.v().set_whole_program(true);	//Implicitly "on" when instrumenting Android, AFAIR.
		Options.v().setPhaseOption("cg", "on");	//"On" by default.
		Options.v().setPhaseOption("cg", "verbose:true");
		Options.v().setPhaseOption("cg", "safe-newinstance:true");
		Options.v().setPhaseOption("cg", "safe-forname:true");
	    Options.v().set_keep_line_number(true);
		Options.v().set_keep_offset(true);

		// replace Soot's printer with our logger (will be overwritten by G.reset(), though)
		// G.v().out = new PrintStream(new LogStream(Logger.getLogger("SOOT"),
		// Level.DEBUG), true);

		Options.v().set_allow_phantom_refs(true);
		Options.v().set_prepend_classpath(true);
		Options.v().set_validate(VALIDATE);

		if (DUMP_JIMPLE) {
			Options.v().set_output_format(Options.output_format_jimple);
		} else {
			Options.v().set_output_format(Options.output_format_dex);
		}
		Options.v().set_process_dir(Collections.singletonList(apk));
		Options.v().set_force_android_jar(androidJAR);
		Options.v().set_android_jars(libJars);
		Options.v().set_src_prec(Options.src_prec_apk);
		Options.v().set_debug(true);
		
		// All packages which are not already in the app's transitive hull but
		// are required by the injected code need to be marked as dynamic.
		Options.v().set_dynamic_package(
				Arrays.asList(new String[] { "acteve.symbolic.", "com.android", "models.", "org.json", "org.apache", "org.w3c",
						"org.xml", "junit", "javax", "javax.crypto"}));

	}

	/**
	 * Main entry point of the Instrumentor.
	 * 
	 * @param args
	 * @throws ZipException
	 * @throws XPathExpressionException
	 * @throws IOException
	 * @throws InterruptedException
	 * @throws ParserConfigurationException
	 * @throws SAXException
	 */	
	

	public static void main(String[] args) throws ZipException, XPathExpressionException, IOException, InterruptedException, ParserConfigurationException, SAXException {
		
		if (DATA_FLOW) {
			//I: run MyTest to get paths (please debug before II)
			  //#### TODO: we can read all following configs from didfail's config file
			soot_infoflow_Base = args[1];
			soot_infoflow_android_Base = args[2];
			String platformdir = args[3];
			String outdir = args[4] + args[5] + ".fd.xml";
			String apkdir = args[0];
			
			String[] args1 = {apkdir,
					platformdir,
					"--nostatic",
					"--aplength",
					"1",
					"--aliasflowins",
					"--out",
					outdir};
			  //#### TODO: presently, we do not print $apk_base.flowdroid.log
			//soot.jimple.infoflow.android.TestApps.MyTest.Mymain(args1);
			mainActsofAPPs = args[5].split("-ac-");
			//org.cert.echoer-ac-org.cert.sendsms-ac-org.cert.WriteFile
			Main.manualPaths.addAll(Arrays.asList(new String[] {
					"<org.cert.sendsms.Button1Listener: void onClick(android.view.View)>",
					"<org.cert.sendsms.MainActivity: void onActivityResult(int,int,android.content.Intent)>",
					"<org.cert.sendsms.MainActivity: void sendSMSMessage(java.lang.String)>",

					"<org.cert.WriteFile.MainActivity: void onActivityResult(int,int,android.content.Intent)>",
					"<org.cert.WriteFile.Button1Listener: java.lang.String getMyLocation()>",
					"<org.cert.WriteFile.Button1Listener: void onClick(android.view.View)>",

					"<org.cert.echoer.MainActivity: void getDataFromIntent()>",
					"<org.cert.echoer.Button1Listener: void <init>(org.cert.echoer.MainActivity)>",
					"<org.cert.echoer.Button1Listener: void onClick(android.view.View)>",
					"<org.cert.echoer.MainActivity: void onCreate(android.os.Bundle)>",
					"<org.cert.echoer.MainActivity: void onResume()>"
			}));
			
			//paths = {    srcInfo={ snkInfo=[meths on path],   ...,   ... },     ...,     ...    }
			
			//II: run cg and //III: add paths[0] to methstoinstrument (before extension)
			  //#### TODO: consider merging I and II in the future)
			
		}
		
		
		soot.G.reset();
		
		config = Config.g();//#### read config
		
		//Clear output dir
		Utils.deleteDir(new File("sootOutput"));
		
		if (args.length<=0 || !new File(args[0]).exists()) {
			printUsage();
			System.exit(-1);
		}
		apk = args[0];
		
		Options.v().set_soot_classpath("./libs/android-19.jar"+":"+libJars+":"+modelClasses + ":" + apk);//#### libs needed to build soot CG? Why specify API 19?
		
		//#### flowdroid
		// inject correct dummy main:
		SetupApplication setupApplication = new SetupApplication(androidJAR, apk);//#### initialize the SetupApplication class instance
		try {
//			   ! ! ! ! ! ! ! ! ! ! ! ! ! ! ! ! ! ! ! ! ! ! ! ! ! ! ! ! ! ! ! !
//			   ! NOTE: calculateSourcesSinksEntrypoints() calls soot.G.reset()
//			   , i.e. it clears all global settings! ! ! ! ! ! ! ! ! ! ! ! ! !
			 
			//#### flowdroid
			setupApplication.calculateSourcesSinksEntrypoints(new HashSet<AndroidMethod>(), new HashSet<AndroidMethod>());
			//#### Calculates  {sources/sinks/entrypoints/callbacks} methods for the APK
			} catch (Exception e) {
				e.printStackTrace();
		}
		
		//#### it does: Options.v().setPhaseOption("cg", "on"); ...
		setSootOptions();//#### restore the class path (changed when calculateSourcesSinksEntrypoints)
		
		//Create dummy main method referencing all entry points
		SootMethod dummyMain = setupApplication.getEntryPointCreator().createDummyMain();

		Scene.v().setEntryPoints(Collections.singletonList(dummyMain));
		Scene.v().addBasicClass(dummyMain.getDeclaringClass().getName(), SootClass.BODIES);
		Scene.v().loadNecessaryClasses();
		
		//Register all application classes for instrumentation
		Chain<SootClass> appclasses = Scene.v().getApplicationClasses();//#### [dummyMainClass, concolicexample.MainActivity$1(i.e.,onclick), models.java.lang.System,...] 
		for (SootClass c:appclasses) {
			methodsToInstrument.addAll(c.getMethods());
		}
		
		//Collect additional classes which will be injected into the app
		//#### inject symbolic classes to app?
		List<String> libClassesToInject = SourceLocator.v().getClassesUnder("./jars/a3t_symbolic.jar");		
		for (String s:libClassesToInject) {
			Scene.v().addBasicClass(s, SootClass.BODIES);
			Scene.v().loadClassAndSupport(s);
			SootClass clazz = Scene.v().forceResolve(s, SootClass.BODIES);
			clazz.setApplicationClass();
		}

		//#### 1. Find OnResume()
		
//		//Get the lifecycle method to instrument
//		ih = new InstrumentationHelper(new File(apk));
//		SootMethod lcMethodToExtend = ih.getDefaultOnResume();
//		if (lcMethodToExtend==null) {
//			lcMethodToExtend = ih.getDefaultOnCreate();
//		}
//		// no onResume/onCreate means no default activity
//		assert lcMethodToExtend!=null:"No default activity found";
		
		//#### 2016.05.31
		/*ih = new InstrumentationHelper(new File(apk));
		HashSet<SootMethod> lcMethodsToExtend = new HashSet<SootMethod>();
		lcMethodsToExtend.addAll(ih.getOnResumeForAllActivities());
		if (lcMethodsToExtend.toString().equals("[null]")) {
			lcMethodsToExtend.addAll(ih.getOnCreateForAllActivities());
		}
		// no onResume/onCreate means no default activity
		assert lcMethodsToExtend!=null:"No activity found";*/
		HashSet<SootMethod> lcMethodsToExtend = new HashSet<SootMethod>();
		int i = 7;
		while (i < args.length){
			InstrumentationHelper iher = new InstrumentationHelper(new File(args[i]));
			ih.add(iher);
			HashSet<SootMethod> lcMethodsToExtender = new HashSet<SootMethod>();
			lcMethodsToExtender.addAll(iher.getOnResumeForAllActivities());
			if (lcMethodsToExtender.toString().equals("[null]")) {
				lcMethodsToExtender.addAll(iher.getOnCreateForAllActivities());
			}
			// no onResume/onCreate means no default activity
			assert lcMethodsToExtender!=null:"No activity found";
			lcMethodsToExtend.addAll(lcMethodsToExtender);
			
			i++;
		}
		
		//#### 2. Extend call graph for findViewById()
		if (!SKIP_CG_EXTENTION) {//#### need know android API (stub?)
			PackManager.v().getPack("wjtp").add(new Transform("wjtp.android", new AndroidCGExtender()));
			//#### extend sootMain class
		}
		
//		//#### 2016.05.31
//		//#### 3. Main transformation (instrumentation) definitions and utils, which will automatically be called by apply()/runPacks()
//		//#### "cg": call graph generation
//		//#### "wjtp": user-defined whole-program transformations
//		//#### apply(): apply configuration ?
//		//#### runPacks(): run job ?
//		if (!SKIP_CONCOLIC_INSTRUMENTATION && !SKIP_ALL_INSTRUMENTATION) {//#### need know symbolics
//			PackManager.v().getPack("wjtp").add(new Transform("wjtp.acteve", new Main()));
//		}
		
			
		// -------------------------------- BEGIN RAFAEL ----------------------------------------------
		CallGraph subGraph = null;
		//#### 4(a). Find paths from life-cycle/ocl entry points to target method (dynamicload) 
		if (LIMIT_TO_CALL_PATH ) {
			 
//			 * 1.	Find all entry points (i.e. "real" entry points according to
//			 *      Android life cycle model that get automatically called by OS)
//			 * 1a.	Add all constructors from View lifecycles (are not provided by EntryPointAnalysis)
//			 * 2)   Find all reachable /target/ methods 
//			 * 3)   Determine all paths from methods in 1) to methods in 2)
//			 * 4)   Instrument only on those paths 
			 
			
			PackManager.v().getPack("cg").apply();//#### didn't call AndroidCGExtender!

			//#### 2016.05.31
			//#### once calls apply(), we have to runPacks() to update cg, or cg won't be the one we want!
			PackManager.v().runPacks();
			
			//1) onResume(), onClick()
			HashSet<SootMethod> entryPoints = new HashSet<SootMethod>(MethodUtils.getCalleesOf(dummyMain));	
			
			//1a)
			SootClass viewClass = Scene.v().getSootClass("android.view.View");
			List<SootClass> views = Scene.v().getActiveHierarchy().getSubclassesOf(viewClass);
			for (SootClass v:views) {
				if (!excludePat.matcher(v.getJavaPackageName()).matches()) {
					try { 	SootMethod immediateConstructor = v.getMethod("void <init>(android.content.Context)"); 
						  	entryPoints.add(immediateConstructor); } catch (RuntimeException rte) {}
					try {	SootMethod inflatingConstructor = v.getMethod("void <init>(android.content.Context,android.util.AttributeSet)");
							entryPoints.add(inflatingConstructor);} catch (RuntimeException rte) {}
					try {	SootMethod inflatingConstructorWStyle = v.getMethod("void <init>(android.content.Context,android.util.AttributeSet,int)");
							entryPoints.add(inflatingConstructorWStyle);} catch (RuntimeException rte) {}
				}
			}

			if (log.isDebugEnabled()) {
				for (SootMethod m : entryPoints){
					log.debug("Entrypoint: {}", m.getSignature());
				}
			}
	
			//#### 2016.06.09
			if (DATA_FLOW) {
				//2)
				// we already have: paths
				
				//3)
				// find extra supporting paths
				//for (List<SootMethod> path1: paths.values()) {
				/*for (SourceInfo src: paths.rowKeySet()) {
					for (SinkInfo snk: paths.columnKeySet()) {
						if (paths.contains(src,snk)) {
							List<SootMethod> taintpath = new ArrayList<SootMethod>();
							for (SootMethod e: paths.get(src,snk)) {
								// the methods in paths (get from flowdroid) does not contain scene context info (i.e., method's containing body)
								taintpath.add(MethodUtils.findMethodWithSignature(e.getSignature()));
							}
							List<SootMethod> fullpath = org.apache.commons.collections.list.SetUniqueList.decorate(new ArrayList<SootMethod>());
							for (SootMethod methOnPath : taintpath){
								// subGraph should contain target API's containing method, e.g., include onClick(), exclude sendSMSMessage()
								fullpath.add(methOnPath);
								subGraph = MethodUtils.findTransitiveCallersOf(methOnPath);//Scene.v().getCallGraph()
								Iterator<MethodOrMethodContext> methodsAlongThePath = subGraph.sourceMethods();
								while (methodsAlongThePath.hasNext()) {
									SootMethod methodAlongThePath = methodsAlongThePath.next().method();
									if(!excludePat.matcher(methodAlongThePath.getDeclaringClass().getName()).matches()){
										fullpath.add(methodAlongThePath);
									}
								}
							}
							fullpaths.put(src, snk, fullpath);
						}
					}
				}*/
				/*
				List<SootMethod> taintpath = new ArrayList<SootMethod>();
				for (String e: Main.manualPaths) {
					// the methods in paths (get from flowdroid) does not contain scene context info (i.e., method's containing body)
					taintpath.add(MethodUtils.findMethodWithSignature(e));
				}
				List<SootMethod> fullpath = org.apache.commons.collections.list.SetUniqueList.decorate(new ArrayList<SootMethod>());
				for (SootMethod methOnPath : taintpath){
					// subGraph should contain target API's containing method, e.g., include onClick(), exclude sendSMSMessage()
					fullpath.add(methOnPath);
					subGraph = MethodUtils.findTransitiveCallersOf(methOnPath);//Scene.v().getCallGraph()
					Iterator<MethodOrMethodContext> methodsAlongThePath = subGraph.sourceMethods();
					while (methodsAlongThePath.hasNext()) {
						SootMethod methodAlongThePath = methodsAlongThePath.next().method();
						if(!excludePat.matcher(methodAlongThePath.getDeclaringClass().getName()).matches()){
							fullpath.add(methodAlongThePath);
						}
					}
				}
				Main.manualFullPaths.addAll(fullpath);*/
				Chain<SootClass> appclasses1 = Scene.v().getApplicationClasses();//#### [dummyMainClass, concolicexample.MainActivity$1(i.e.,onclick), models.java.lang.System,...] 
				for (SootClass c:appclasses1) {
					for (SootMethod m:c.getMethods()) {
						if (manualPaths.contains(m.getSignature())){
							manualFullPaths.add(m);
						}
					}
				}
				
				//#### TODO: print path ...
				
				//#### 4(b). Presently, we instrument all paths. 
				//"Reset" classesToInstrument to those along the CP
				methodsToInstrument = new HashSet<SootMethod>();
				/*for (SourceInfo src: fullpaths.rowKeySet()) {
					for (SinkInfo snk: fullpaths.columnKeySet()) {
						if (fullpaths.contains(src,snk)) {
							methodsToInstrument.addAll(fullpaths.get(src,snk));
						}
					}
				}*/
				methodsToInstrument.addAll(Main.manualFullPaths);
			}
			else {
				//2)
				List<SootMethod> targetMethods = MethodUtils.findReflectiveLoadingMethods(entryPoints);
				if (DEBUG) {//#### not set, so no print
					log.debug("Found the following target methods:");
					for (SootMethod m : targetMethods){
						log.debug("  Signature: {}", m.getSignature());
					}
				}
				
				//3)
				//we have all SootMethods now which might be used to load classes at runtime. Now get the classes on the paths to them:
				HashMap<SootMethod, List<SootMethod>> pathsToGoal = new HashMap<SootMethod, List<SootMethod>>();
				for (SootMethod targetMeth : targetMethods){
					List<SootMethod> path = new ArrayList<SootMethod>();
	//				//add the declaring class because developers might inherit & extend from base class loaders
	//				if(!excludePat.matcher(targetMeth.getDeclaringClass().getName()).matches())
	//					path.add(targetMeth.getDeclaringClass());
					//add all methods on the way to the call:
					//#### all methods (immediately/transitively) reachable to targetmethod
					//#### callback registration != method call
					
	//				log.debug("wtj-ext");
	//				log.debug(Scene.v().getCallGraph().toString());
	//				log.debug("jtw-ext");
					
					
					subGraph = MethodUtils.findTransitiveCallersOf(targetMeth);//Scene.v().getCallGraph()
					Iterator<MethodOrMethodContext> methodsAlongThePath = subGraph.sourceMethods();
					while (methodsAlongThePath.hasNext()) {
						SootMethod methodAlongThePath = methodsAlongThePath.next().method();
						if(!excludePat.matcher(methodAlongThePath.getDeclaringClass().getName()).matches()){
							path.add(methodAlongThePath);
						}
					}
					pathsToGoal.put(targetMeth, path);
				}
				
				//#### print path
				if (DEBUG) {
					for (SootMethod goal:pathsToGoal.keySet()) {
						log.debug("{} methods along the path to {}", pathsToGoal.get(goal).size(), goal.getSignature());
						List<SootMethod> along = pathsToGoal.get(goal);
						for (SootMethod m:along) {
							log.debug("  {}", m.getSignature());
						}
					}
				}
				
				//#### 4(b). to instrument the path
				//"Reset" classesToInstrument to those along the CP
				methodsToInstrument = new HashSet<SootMethod>();
				for (List<SootMethod> path:pathsToGoal.values()) {
					methodsToInstrument.addAll(path);
				}		
			}
		}
		// -------------------------------- END RAFAEL ----------------------------------------------

		//#### 2016.05.31
		if (!SKIP_CONCOLIC_INSTRUMENTATION && !SKIP_ALL_INSTRUMENTATION) {//#### need know symbolics
			PackManager.v().getPack("wjtp").add(new Transform("wjtp.acteve", new Main()));
		}
		
		if (!SKIP_ALL_INSTRUMENTATION) {
			try {
				if (subGraph!=null) { // if LIMIT_TO_CALL_PATH has been applied
					HashSet<SootClass> entryClasses = new HashSet<SootClass>();
					//#### edges that have dummyMain as their source method
					//#### those methods' declaringclass are also entry
					//#### BUT entryClasses is never used afterwards!
					for (Iterator<Edge> entryEdges = subGraph.edgesOutOf(Scene.v().getMethod("<dummyMainClass: void dummyMainMethod()>"));entryEdges.hasNext();) {
						entryClasses.add(entryEdges.next().tgt().getDeclaringClass());
					}
				}
				//#### 5. insert all calls at the end of onResume()
				//#### intent!!!, onClick, ...
				//#### the only difference between LIMIT_TO_CALL_PATH=true/false is "methodsToInstrument"
				//ih.insertCallsToLifecycleMethods(lcMethodToExtend, methodsToInstrument);
				//#### 2016.05.31
				//#### different activities may be confused?
				for (SootMethod lcm: lcMethodsToExtend) {
					if (lcm != null) {
						for (InstrumentationHelper iher: ih) {
							if (iher.getPackagename().equals(lcm.getDeclaringClass().getPackageName())) {
								Set<SootMethod> methodsToInstrument2 = new HashSet<SootMethod>();
								for (SootMethod m: methodsToInstrument) {
									if (m.getDeclaringClass().getPackageName().equals(lcm.getDeclaringClass().getPackageName()))
										//in the same package (just look up class prefix for simplicity, as we only instrument ocl and intent)
										methodsToInstrument2.add(m);
								}
								iher.insertCallsToLifecycleMethods(lcm, methodsToInstrument2);
							}
						}
					}
				}
			} catch (Exception e) {
				log.error("Exception while inserting calls to lifecycle methods:", e);
			}
			
			//build new call graph now that we have paths to UI-induced method calls:
			PackManager.v().getPack("cg").apply();// didn't call CGExtender
		}

		//#### heap
		//#### add accesss method for all classes on the path
		//#### access method is mainly for nonomous container class (i.e., component ...)
		//#### non-nonomous class already can be instrumted
		
//		LinkedHashSet<SootClass> mainClass = ih.getMainActivity();
//		for (SootClass cm:mainClass) {
//			for (Iterator<SootMethod> it = cm.methodIterator(); it.hasNext();) {
//				SootMethod meths = (SootMethod) it.next();
//				if (meths.getName().contains("access$"))
//					methodsToInstrument.add(meths);
//			}
//		}
		List<SootMethod> methtoadd = new ArrayList<SootMethod>();
		for (SootMethod method:methodsToInstrument){
			SwitchTransformer.transform(method);
			Body body = method.retrieveActiveBody();		
			G.editor.newBody(body, method);
			while (G.editor.hasNext()) {
				Stmt s = G.editor.next();
				if (s.containsInvokeExpr()) {
					InvokeExpr ie = s.getInvokeExpr();
					SootMethod callee = ie.getMethod();
					if (callee.getName().contains("access$"))
						methtoadd.add(callee);
				}
			}
		}
		methodsToInstrument.addAll(methtoadd);
		
		
		//dump all methods for debugging:
		if (log.isDebugEnabled()) {
			List<SootMethod> allMethods = MethodUtils.getAllReachableMethods();
			log.debug("All methods in the scene:");
			for (SootMethod m : allMethods)
				log.debug("\t{}", m.getSignature());
		}

		//Start instrumentation
		//#### soot: global transformation
		//#### calls internalTransform of both main and AndroidCGExtender
		  // CGExt: extend CG
		  // main: insert calls at end of onResume, basing on CG
		  // As pathtogoal and others also depend on CG, runPacks() without main first?
		PackManager.v().runPacks();
		PackManager.v().writeOutput();//#### soot: output results; write dex (apk)
		
		
//		log.debug("wtj-ext");
//		log.debug(Scene.v().getCallGraph().toString());
//		log.debug("jtw-ext");
		
		//Just nice to have: Print Callgraph to a .dot file
		if (DUMP_CG_TO_DOT) {
			log.debug("Printing call graph to .dot file");
			MethodUtils.printCGtoDOT(Scene.v().getCallGraph(), "main");
		}
		
		String outputApk = "sootOutput/"+new File(apk).getName();
		if (new File(outputApk).exists()) {
			File f = new File(outputApk);
			
			//Add permission to access sdcard
			if (!OMIT_MANIFEST_MODIFICATION) {
				HashMap<String, String> replacements = new HashMap<String, String>();
				replacements.put("</manifest>", "<uses-permission android:name=\"android.permission.WRITE_EXTERNAL_STORAGE\" /> </manifest>");
				f = InstrumentationHelper.adaptManifest(f.getAbsolutePath(), replacements);				
			}
			
			//Sign the APK
			signAPK(f.getAbsolutePath());
			
			log.info("Done. Have fun with {}", f.getAbsolutePath());//#### the ultimate apk
			
			//Handover to explorer
			String appPkgName = ih.get(0).getPackagename();
			
			//#### 2016.06.20 replace mainActivity with arbitrary component
			String mainActivity;
			if (!Main.SEGMENTED) {
				mainActivity = ih.get(0).getDefaultActivities().iterator().next();
			} else {
				mainActivity = args[6];
			}
			
			//#### acteve.explorer.utils already imported acteve.explorer, so no need import again?
			acteve.explorer.Main.main(new String[] {f.getAbsolutePath(), appPkgName, mainActivity});
			//#### {"/home/julian/workspace/ConDroid/sootOutput/concolicexample_modified.apk","com.example.de.fhg.aisec.concolicexample","MainActivity"}
		} else {
			log.error("ERROR: " + outputApk + " does not exist");
		}
	}

	
	private static void printUsage() {
		System.out.println("Usage: instrumenter <apk>");
		System.out.println("  apk:    APK file to prepare");
	}


	private static void signAPK(String apk) {
		try {
			// jarsigner is part of the Java SDK
			log.info("Signing {} ...", apk);
			String cmd = "jarsigner -verbose -digestalg SHA1 -sigalg MD5withRSA -storepass android -keystore "+System.getProperty("user.home")+"/.android/debug.keystore "
					+ apk + " androiddebugkey";
			log.debug("Calling {}", cmd);
			Process p = Runtime.getRuntime().exec(cmd);
			printProcessOutput(p);

			// zipalign is part of the Android SDK
//			log.info("Zipalign ...", apk);
//			cmd = "zipalign -v 4 " + apk + " " + new File(apk).getName() + "_signed.apk";
//			log.debug(cmd);
//			p = Runtime.getRuntime().exec(cmd);
//			printProcessOutput(p);
		} catch (IOException e) {
			log.error(e.getMessage(), e);
		}
	}
	
	private static void printProcessOutput(Process p) throws IOException{
		String line;
		BufferedReader input = new BufferedReader(new InputStreamReader(p.getInputStream()));
		while ((line = input.readLine()) != null) {
		  System.out.println(line);
		}
		input.close();
		
		input = new BufferedReader(new InputStreamReader(p.getErrorStream()));
		while ((line = input.readLine()) != null) {
		  System.out.println(line);
		}
		input.close();
	}

	static boolean isInstrumented(SootMethod m) {
		return methodsToInstrument.contains(m);
	}

	
//	 *
//	 * Load a soot class from Jimple. 
//	 * 
//	 * @param f
//	 * @param className
//	 * @return
	 
	public static SootClass loadFromJimple(File f, String className) {
		try {
			// Create FIP for jimple file
			FileInputStream fip = new FileInputStream(f);

			// Load from Jimple file
			JimpleClassSource jcs = new JimpleClassSource(className, fip);
			SootClass sc = new SootClass(className, Modifier.PUBLIC);
			jcs.resolve(sc);			
			return sc;
		} catch (Throwable t) {
			t.printStackTrace();
		}
		return null;
	}
	
//	 *
//	 * Load class from jimple files in a directory.
//	 * 
//	 * @param dirname
//	 * @return
//	 *
	public static List<SootClass> loadFromJimples(String dirname) {
		File dir = new File(dirname);
		if (!dir.exists() || !dir.isDirectory())
			return null;
		List<SootClass> jimples = new ArrayList<SootClass>();
		for (File f : dir.listFiles())
			jimples.add(loadFromJimple(f, f.getName().replace(".jimple", "")));
		return jimples;
	}
}
	

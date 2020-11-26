import java.io.*;
import java.util.*;
import java.util.regex.Pattern;
import com.ibm.wala.classLoader.ShrikeBTMethod;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.Entrypoint;
import com.ibm.wala.ipa.callgraph.cha.CHACallGraph;
import com.ibm.wala.ipa.callgraph.impl.AllApplicationEntrypoints;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyFactory;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.shrikeCT.InvalidClassFileException;
import com.ibm.wala.types.annotations.Annotation;
import com.ibm.wala.util.CancelException;

public class AutomatedTesting {
    public static void main(String[] args) throws IOException, ClassHierarchyException,InvalidClassFileException,  CancelException {
        AutomatedTesting ts = new AutomatedTesting(args[1], args[2]);
        ts.select(args[0].charAt(1));
    }

    private final HashSet<String> allFindedClasses = new HashSet<String>();  //all the finded class
    private final HashSet<String> testListedMethods = new HashSet<String>(); //test listed method
    private final HashSet<String> allListedMethods = new HashSet<String>();  //listed method
    private final HashMap<String, List<String>> callerRelation = new HashMap<String, List<String>>(); // key为方法，value为所有直接调用了key方法的方法
    private final ArrayList<String> changeInfo = new ArrayList<String>(); // 记录所有的变更信息
    public final HashMap<String, List<String>> classDependencies = new HashMap<>();  // 类级别依赖信息，key为类名，value为所有直接依赖该类的类名
    public final HashMap<String, List<String>> methodDependencies = new HashMap<>(); // 方法级别依赖，key为方法名，value为所有直接依赖该方法的方法名
    private final String infoPath;
    private final String endPath;
    private final String rootPath = "D:\\AutomatedTesting\\Project\\src\\main\\resources\\scope.txt";
    private final String exclusionPath = "D:\\AutomatedTesting\\Project\\src\\main\\resources\\exclusion.txt";
    public AutomatedTesting(String endPath, String infoPath) {
        this.endPath = endPath;
        this.infoPath = infoPath;
    }

    //main recursive select by class
    public void byClass(HashSet<String> relatedClasses, String searchClass) {
        for (String callee : callerRelation.keySet()) {
            if (callee.split(" ")[0].equals(searchClass)) {
                for (String caller : callerRelation.get(callee)) {
                    relatedClasses.add(caller.split(" ")[0]);
                    if (relatedClasses.contains(caller.split(" ")[0]))
                        continue;
                    // recursive to find caller related class，find
                    byClass(relatedClasses, caller.split(" ")[0]);
                }
            }
        }
    }
    //gather set of TestCase to a fileWriter
    public void methodsStoring(HashSet<String> selectedMethods, String filename) {
        try {
            int count = 0;
            File file = new File(filename);
            FileWriter fileWriter = new FileWriter(file);
            BufferedWriter bufferedWriter = new BufferedWriter(fileWriter);
            for (String string : selectedMethods) {
                if (testListedMethods.contains(string)){
                    bufferedWriter.write(string + "\n");
                    count ++;
                }
            }
            bufferedWriter.flush();
            System.out.print(count);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public void getMethodDependencies() {
        for (String s : callerRelation.keySet()) {
            String callee = s.split(" ")[1];
            if (!allFindedClasses.contains(s.split(" ")[0]))
                continue;
            if (!methodDependencies.containsKey(callee)) {
                List<String> list = new ArrayList<>();
                methodDependencies.put(callee, list);
            }
            for (String string : callerRelation.get(s)) {
                String caller = string.split(" ")[1];
                if (!methodDependencies.get(callee).contains(caller)) {
                    if (!allFindedClasses.contains(string.split(" ")[0]))
                        continue;
                    methodDependencies.get(callee).add(caller);
                }
            }
        }
        try {
            File file = new File("./method-dependencies.dot");
            FileWriter fileWriter = new FileWriter(file);
            BufferedWriter bufferedWriter = new BufferedWriter(fileWriter);
            bufferedWriter.write("digraph dependencies {\n");
            for (String string : methodDependencies.keySet()) {
                for (String s : methodDependencies.get(string)) {
                    bufferedWriter.write("\t");
                    bufferedWriter.write("\"" + string + "\" -> \"" + s + "\";\n");
                }
            }
            bufferedWriter.write("}");
            bufferedWriter.flush();
        } catch (IOException e) {
            e.printStackTrace();
        }

    }

    public void byMethod(HashSet<String> relatedMethod, String searchMethod) {
        HashSet<String> newMethod = new HashSet<String>();
        if (!this.callerRelation.containsKey(searchMethod))
            return;
        for (String s : this.callerRelation.get(searchMethod)) {
            if (!relatedMethod.contains(s)) {
                relatedMethod.add(s);
                newMethod.add(s);
            }
        }
        for (String s : newMethod) {
            byMethod(relatedMethod, s);
        }
    }

    public void buildcallerRelation(CHACallGraph cg) throws InvalidClassFileException {// 遍历cg中所有的节点
        for (CGNode node : cg) {
            if (node.getMethod() instanceof ShrikeBTMethod) {
                ShrikeBTMethod method = (ShrikeBTMethod) node.getMethod();
                if ("Application".equals(method.getDeclaringClass().getClassLoader().toString())) {
                    String classInnerName = method.getDeclaringClass().getName().toString();
                    String signature = method.getSignature();
                    String caller = classInnerName + " " + signature;
                    String pattern = "Annotation type <Application,Lorg/junit/Test>.*";
                    for (Annotation annotationType : method.getAnnotations()) {
                        if (Pattern.matches(pattern, annotationType.toString())) {
                            testListedMethods.add(caller);
                            break;
                        }
                    }

                    for (CallSiteReference m : method.getCallSites()) {
                        String calledClass = m.getDeclaredTarget().toString().replace(" ", "").split(",")[1].split("\\$")[0];
                        String calledMethod = m.getDeclaredTarget().getSignature();
                        String callee = calledClass + " " + calledMethod;

                        if (callerRelation.containsKey(callee)) {
                            if (!callerRelation.get(callee).contains(caller)) {
                                callerRelation.get(callee).add(caller);
                            }
                        } else {
                            List<String> list = new ArrayList<String>();
                            list.add(caller);
                            callerRelation.put(callee, list);
                        }
                    }
                }
            }
        }

        System.out.println("Well, show call relation");
        for (String callee : callerRelation.keySet()) {
            System.out.println(callee);
            for (String s : callerRelation.get(callee)) {
                System.out.println(s);
            }
            System.out.println();
        }
        //All the methods of callerRelation to allListedMethods
        for (String callee : callerRelation.keySet()) {
            allListedMethods.add(callee);
            allListedMethods.addAll(callerRelation.get(callee));
        }
    }

    public static Map<String, HashSet<String>> readChangeInfo(String changeInfo) {
        Map<String, HashSet<String>> hashMap = new HashMap<String, HashSet<String>>();
        HashSet<String> set = new HashSet<>();
        String line;
        String[] tmp;
        try {
            BufferedReader reader = new BufferedReader(new FileReader(changeInfo));
            while ((line = reader.readLine()) != null) {
                tmp = line.split(" ");
                if (tmp.length != 2) {
                    System.out.println("wrong with change_info.txt format");
                    break;
                }
                //索引0存放类，索引1存放方法
                if (hashMap.get(tmp[0]) != null) {
                    // key存在
                    set = hashMap.get(tmp[0]);
                    set.add(tmp[1]);
                    hashMap.put(tmp[0], set);
                    set = new HashSet<>();
                } else {
                    set.add(tmp[1]);
                    hashMap.put(tmp[0], set);
                    set = new HashSet<>();
                }
            }
        } catch (Exception e) {
            System.out.println(e.getMessage());
        }
        return hashMap;
    }

    public void getClassDependencies() {
        for (String s : callerRelation.keySet()) {
            String callee = s.split(" ")[0];
            if (!allFindedClasses.contains(callee))
                continue;
            if (!classDependencies.containsKey(callee)) {
                List<String> list = new ArrayList<>();
                classDependencies.put(callee, list);
            }
            for (String string : callerRelation.get(s)) {
                String caller = string.split(" ")[0];
                if (!classDependencies.get(callee).contains(caller)) {
                    if (!allFindedClasses.contains(caller))
                        continue;
                    classDependencies.get(callee).add(caller);
                }
            }
        }
        try {
            File file = new File("./class-dependencies.dot");
            FileWriter fileWriter = new FileWriter(file);
            BufferedWriter bufferedWriter = new BufferedWriter(fileWriter);
            bufferedWriter.write("digraph dependencies {\n");
            for (String string : classDependencies.keySet()) {
                for (String s : classDependencies.get(string)) {
                    bufferedWriter.write("\t");
                    bufferedWriter.write("\"" + string + "\" -> \"" + s + "\";\n");
                }
            }
            bufferedWriter.write("}");
            bufferedWriter.flush();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public void select(char selectOption) throws IOException, InvalidClassFileException, ClassHierarchyException, CancelException {
        String sourcedirPath = this.endPath + "\\classes\\net\\mooctest";
        String testdirPath = this.endPath + "\\test-classes\\net\\mooctest";
        File sourcedir = new File(sourcedirPath);
        File testdir = new File(testdirPath);
        File[] sourceFiles = sourcedir.listFiles();
        File[] testFiles = testdir.listFiles();
        ClassLoader classLoader = AutomatedTesting.class.getClassLoader();
        AnalysisScope scope = AnalysisScopeReader.readJavaScope(this.rootPath, new File(this.exclusionPath), classLoader);
        if (sourceFiles != null) {
            for (File f : sourceFiles) {
                scope.addClassFileToScope(ClassLoaderReference.Application, f);
            }
        }
        if (testFiles != null) {
            for (File f : testFiles) {
                scope.addClassFileToScope(ClassLoaderReference.Application, f);
            }
        }
        ClassHierarchy cha = ClassHierarchyFactory.makeWithRoot(scope);
        Iterable<Entrypoint> eps = new AllApplicationEntrypoints(scope, cha);
        CHACallGraph cg = new CHACallGraph(cha);
        cg.init(eps);
        for (CGNode node : cg) {
            if (node.getMethod() instanceof ShrikeBTMethod) {
                ShrikeBTMethod method = (ShrikeBTMethod) node.getMethod();
                if ("Application".equals(method.getDeclaringClass().getClassLoader().toString())) {
                    String classInnerName = method.getDeclaringClass().getName().toString();
                    this.allFindedClasses.add(classInnerName.split("\\$")[0]);
                }
            }
        }
        this.buildcallerRelation(cg);
        try {
            BufferedReader in = new BufferedReader(new FileReader(this.infoPath));
            String line;
            while ((line = in.readLine()) != null) {
                this.changeInfo.add(line);
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
        //factory c or m
        if (selectOption == 'c') {
            HashSet<String> relatedClasses = new HashSet<String>();
            HashSet<String> selectedMethods = new HashSet<String>();
            for (String s : changeInfo) {
                String searchClass = s.split(" ")[0];
                relatedClasses.add(searchClass);
                byClass(relatedClasses, searchClass);
            }

            for (String s : allListedMethods) {
                if (relatedClasses.contains(s.split(" ")[0])) {
                    selectedMethods.add(s);
                }
            }
            this.methodsStoring(selectedMethods, "./selection-class.txt");
        } else if (selectOption == 'm') {
            HashSet<String> selectedMethods = new HashSet<String>();
            for (String s : changeInfo) {
                HashSet<String> relatedMethods = new HashSet<String>();
                byMethod(relatedMethods, s);
                selectedMethods.addAll(relatedMethods);
            }
            this.methodsStoring(selectedMethods, "./selection-method.txt");
        } else {
            System.err.println("Unknown select option" + selectOption);
        }
        this.getClassDependencies();
        this.getMethodDependencies();
    }

}

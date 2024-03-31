import java.util.*;
import soot.*;
import soot.jimple.AnyNewExpr;
import soot.jimple.internal.*;
import soot.jimple.*;
import soot.toolkits.graph.*;
import soot.toolkits.scalar.BackwardFlowAnalysis;
import soot.toolkits.scalar.FlowSet;

class Box {
	int line;
    Map<String, Set<Box>> fields;
    boolean dummy;
    boolean escape;
    Box(int line, boolean dummy){
        this.line = line;
        fields = new HashMap<>();
        this.dummy = dummy;
        if(dummy) escape = true;
        else escape = false;
    }
    @Override
    public String toString(){
        String s = Integer.toString(line);
        s = s + "-" + escape + dummy;
        for (Map.Entry<String, Set<Box>> entry : fields.entrySet())  
            s = s + " " + entry.getKey() + " " + entry.getValue();
        return s;
    }
}

public class AnalysisTransformer extends BodyTransformer {
    public static SortedSet<String> strings = new TreeSet<>();
    @Override
    protected void internalTransform(Body body, String phaseName, Map<String, String> options) {

        String methodName = body.getMethod().getName();
        String className = body.getMethod().getDeclaringClass().getName();
        
        // Construct CFG for the current method's body
        ExceptionalUnitGraph cfg = new ExceptionalUnitGraph(body);
        
        // Point to Map
        Map<Unit, Map<String, Set<Box>>> out = new HashMap<>();
        SortedMap<Integer, Box> boxes = new TreeMap<>();
        pointsToGraph(body, cfg, out, boxes);
        
        // Print Escaping Lines
        String s = className + ":" + methodName;
        int cnt = 0;
        for (Map.Entry<Integer, Box> entry : boxes.entrySet()) {
            int line = entry.getKey();
            Box box = entry.getValue();
            if(!box.dummy && box.escape){
                s = s + " " + line;
                cnt++;
            }
        }
        if (!methodName.equals("<init>") && cnt>0) {
            strings.add(s);
        }
    }


    private void pointsToGraph(Body body, ExceptionalUnitGraph cfg, Map<Unit, Map<String, Set<Box>>> out, SortedMap<Integer, Box> boxes){
        // Initialize the points-to graph
        for (Unit unit : cfg) {
            Map<String, Set<Box>> ptg = new HashMap<>();
            for (Local local : body.getLocals()) {
                ptg.put(local.getName(), new HashSet<>());
            }
            // for (Value param : body.getParameterLocals()) {
            //     if (param instanceof Local) {
            //         Local localParam = (Local) param;
            //         Set<Box> pts = new HashSet<>();
            //         Box dummybox = createBox(unit, true, boxes);
            //         pts.add(dummybox);
            //         ptg.put(localParam.getName(), pts);
            //     }
            // }
            out.put(unit, ptg);
        }

        Queue<Unit> worklist = new LinkedList<>();
        worklist.addAll(cfg.getHeads());

        Map<String, Set<Box>> lastOut = new HashMap<>();
        while (!worklist.isEmpty()) {
            Unit unit = worklist.remove();
            Map<String, Set<Box>> oldout = out.get(unit);
            Map<String, Set<Box>> newout = getNewOut(unit, cfg, out, boxes);

            // Check if OUT set has changed
            if (!oldout.equals(newout)) {
                // System.out.println("Unit: " + unit);
                // System.out.println("NewOut: " + newout);
                out.put(unit, newout);
                for (Unit succ : cfg.getSuccsOf(unit)) {
                    worklist.add(succ);
                }
                // lastOut = newout;
                // escapeBFS(newout);
            }
        }
        // escapeBFS(lastOut);
        // System.out.println("Points-to Map: " + out);
    }


    private Map<String, Set<Box>> getNewOut(Unit unit, ExceptionalUnitGraph cfg, Map<Unit, Map<String, Set<Box>>> out, SortedMap<Integer, Box> boxes){
        Map<String, Set<Box>> newout = new HashMap<>();
        for (Unit pred : cfg.getPredsOf(unit)) {
            Map<String, Set<Box>> predout = out.get(pred);
            for (Map.Entry<String, Set<Box>> entry : predout.entrySet()) {
                String localName = entry.getKey();
                Set<Box> predSet = entry.getValue();
                if (newout.containsKey(localName)) {
                    newout.get(localName).addAll(predSet);
                } else {
                    newout.put(localName, new HashSet<>(predSet));
                }
            }
        }
        // process the stmt
        if (unit instanceof IdentityStmt) {
            IdentityStmt identityStmt = (IdentityStmt) unit;
            Value leftOp = identityStmt.getLeftOp();
            Value rightOp = identityStmt.getRightOp();
            if (leftOp instanceof Local) {
                Local leftLocal = (Local) leftOp;
                if (rightOp instanceof ParameterRef) {
                    ParameterRef parameterRef = (ParameterRef) rightOp;
                    Set<Box> paramPointsTo = new HashSet<>();
                    Box dummybox = createBox(unit, true, boxes);
                    paramPointsTo.add(dummybox);
                    newout.put(leftLocal.getName(), paramPointsTo);
                }
                else if (rightOp instanceof ThisRef) {
                    ThisRef thisRef = (ThisRef) rightOp;
                    Set<Box> thisPointsTo = new HashSet<>();
                    Box dummybox = createBox(unit, true, boxes);
                    thisPointsTo.add(dummybox);
                    newout.put(leftLocal.getName(), thisPointsTo);
                }
            }
        }
        if (unit instanceof AssignStmt) {
            AssignStmt assignStmt = (AssignStmt) unit;
            Value leftOp = assignStmt.getLeftOp();
            Value rightOp = assignStmt.getRightOp();
            if (leftOp instanceof StaticFieldRef) {
                // Handle assignment to a global variable
                StaticFieldRef globalVarRef = (StaticFieldRef) leftOp;
                SootField globalField = globalVarRef.getField();
                Local rightLocal = (Local) rightOp;
                Set<Box> pointsToSet = newout.getOrDefault(rightLocal.getName(), new HashSet<>());
                newout.put(globalField.getName(), pointsToSet);
                markEscape(rightOp, newout);
            }
            else if (leftOp instanceof Local) {
                Local leftLocal = (Local) leftOp;
                String leftName = leftLocal.getName();
                if (rightOp instanceof StaticInvokeExpr) {
                    StaticInvokeExpr staticInvokeExpr = (StaticInvokeExpr) rightOp;
                    for (Value arg : staticInvokeExpr.getArgs()) {
                        markEscape(arg, newout);
                    }
                    Set<Box> invokePointsTo = new HashSet<>();
                    Box dummybox = createBox(unit, true, boxes);
                    invokePointsTo.add(dummybox);
                    newout.put(leftName, invokePointsTo);
                } 
                else if (rightOp instanceof StaticFieldRef) {
                    StaticFieldRef globalVarRef = (StaticFieldRef) rightOp;
                    SootField globalField = globalVarRef.getField();
                    String globalVarName = globalField.getName();
                    Set<Box> rightPointsTo = new HashSet<>();
                    if (newout.containsKey(globalVarName)) {
                        rightPointsTo.addAll(newout.get(globalVarName));
                    } else {
                        Box dummybox = createBox(unit, true, boxes);
                        rightPointsTo.add(dummybox);
                        newout.put(globalVarName, rightPointsTo);
                    }
                    newout.put(leftName, rightPointsTo);
                }
                else if (rightOp instanceof NewExpr) {
                    Box box = createBox(unit, false, boxes);
                    Set<Box> rightPointsTo = new HashSet<>();
                    rightPointsTo.add(box);
                    if(isLeftEscaping(leftLocal, newout)){
                        box.escape = true;
                    }
                    newout.put(leftName, rightPointsTo);
                }
                else if (rightOp instanceof Local) {
                    Local rightLocal = (Local) rightOp;
                    Set<Box> rightPointsTo = newout.getOrDefault(rightLocal.getName(), new HashSet<>());
                    if(isLeftEscaping(leftLocal, newout)){
                        escapeBoxSet(rightPointsTo);
                    }
                    newout.put(leftName, rightPointsTo);
                }
                else if (rightOp instanceof InstanceFieldRef){
                    InstanceFieldRef fieldRef = (InstanceFieldRef) rightOp;
                    Local baseLocal = (Local) fieldRef.getBase();
                    String fieldName = fieldRef.getField().getName();
                    Set<Box> basePointsTo = newout.get(baseLocal.getName());
                    if (basePointsTo != null) {
                        for (Box box : basePointsTo) {
                            Set<Box> fieldValues = box.fields.get(fieldName);
                            if (newout.containsKey(leftName)) {
                                if (fieldValues != null) {
                                    newout.get(leftName).addAll(fieldValues);
                                } 
                                else if(box.dummy){
                                    Set<Box> pts = new HashSet<>();
                                    Box dummybox = createBox(unit, true, boxes);
                                    pts.add(dummybox);
                                    newout.get(leftName).addAll(pts);
                                }
                                else {
                                    newout.get(leftName).addAll(new HashSet<>());
                                }
                            }
                            else {
                                if (fieldValues != null) {
                                    newout.put(leftName,fieldValues);
                                } 
                                else if(box.dummy){
                                    Set<Box> pts = new HashSet<>();
                                    Box dummybox = createBox(unit, true, boxes);
                                    pts.add(dummybox);
                                    newout.put(leftName,pts);
                                }
                                else {
                                    newout.put(leftName,new HashSet<>());
                                }
                            }
                        }
                    }
                }
                else if (rightOp instanceof ArrayRef){
                    ArrayRef fieldRef = (ArrayRef) rightOp;
                    Local baseLocal = (Local) fieldRef.getBase();
                    String fieldName = "[]";
                    Set<Box> basePointsTo = newout.get(baseLocal.getName());
                    if (basePointsTo != null) {
                        for (Box box : basePointsTo) {
                            Set<Box> fieldValues = box.fields.get(fieldName);
                            if (newout.containsKey(leftName)) {
                                if (fieldValues != null) {
                                    newout.get(leftName).addAll(fieldValues);
                                } 
                                else if(box.dummy){
                                    Set<Box> pts = new HashSet<>();
                                    Box dummybox = createBox(unit, true, boxes);
                                    pts.add(dummybox);
                                    newout.get(leftName).addAll(pts);
                                }
                                else {
                                    newout.get(leftName).addAll(new HashSet<>());
                                }
                            }
                            else {
                                if (fieldValues != null) {
                                    newout.put(leftName,fieldValues);
                                } 
                                else if(box.dummy){
                                    Set<Box> pts = new HashSet<>();
                                    Box dummybox = createBox(unit, true, boxes);
                                    pts.add(dummybox);
                                    newout.put(leftName,pts);
                                }
                                else {
                                    newout.put(leftName,new HashSet<>());
                                }
                            }
                        }
                    }
                }
            }
            else if (leftOp instanceof InstanceFieldRef) {
                InstanceFieldRef fieldRef = (InstanceFieldRef) leftOp;
                Local baseLocal = (Local) fieldRef.getBase();
                String fieldName = fieldRef.getField().getName();
                Set<Box> rightPointsTo = new HashSet<>();
                if (rightOp instanceof NewExpr) {
                    Box box = createBox(unit, false, boxes);
                    rightPointsTo.add(box);
                }
                else if (rightOp instanceof Local) {
                    Local rightLocal = (Local) rightOp;
                    rightPointsTo = newout.getOrDefault(rightLocal.getName(), new HashSet<>());
                }
                Set<Box> basePointsTo = newout.get(baseLocal.getName());
                if (basePointsTo != null) {
                    boolean baseEscape = false;
                    for (Box box : basePointsTo) {
                        if(box.escape){
                            escapeBoxSet(rightPointsTo);
                            baseEscape = true;
                            break;
                        }
                    }
                    for (Box box : basePointsTo) {
                        if (box.fields.containsKey(fieldName)) {
                            Set<Box> fieldPointsTo = box.fields.get(fieldName);
                            if(baseEscape){
                                escapeBoxSet(fieldPointsTo);
                            }
                            for(Box fieldbox : fieldPointsTo){
                                if(fieldbox.escape == true) escapeBoxSet(rightPointsTo);
                            }
                            fieldPointsTo.addAll(rightPointsTo);
                        }
                        else if(box.dummy){
                            Set<Box> pts = new HashSet<>(rightPointsTo);
                            Box dummybox = createBox(unit, true, boxes);
                            pts.add(dummybox);
                            box.fields.put(fieldName, pts);
                        }
                        else{
                            box.fields.put(fieldName, new HashSet<>(rightPointsTo));
                        }
                    }
                }
            }
            else if (leftOp instanceof ArrayRef) {
                ArrayRef fieldRef = (ArrayRef) leftOp;
                Local baseLocal = (Local) fieldRef.getBase();
                String fieldName = "[]";
                Set<Box> rightPointsTo = new HashSet<>();
                if (rightOp instanceof NewExpr) {
                    Box box = createBox(unit, false, boxes);
                    rightPointsTo.add(box);
                }
                else if (rightOp instanceof Local) {
                    Local rightLocal = (Local) rightOp;
                    rightPointsTo = newout.getOrDefault(rightLocal.getName(), new HashSet<>());
                }
                Set<Box> basePointsTo = newout.get(baseLocal.getName());
                if (basePointsTo != null) {
                    boolean baseEscape = false;
                    for (Box box : basePointsTo) {
                        if(box.escape){
                            escapeBoxSet(rightPointsTo);
                            baseEscape = true;
                            break;
                        }
                    }
                    for (Box box : basePointsTo) {
                        if (box.fields.containsKey(fieldName)) {
                            Set<Box> fieldPointsTo = box.fields.get(fieldName);
                            if(baseEscape){
                                escapeBoxSet(fieldPointsTo);
                            }
                            for(Box fieldbox : fieldPointsTo){
                                if(fieldbox.escape == true) escapeBoxSet(rightPointsTo);
                            }
                            fieldPointsTo.addAll(rightPointsTo);
                        }
                        else if(box.dummy){
                            Set<Box> pts = new HashSet<>(rightPointsTo);
                            Box dummybox = createBox(unit, true, boxes);
                            pts.add(dummybox);
                            box.fields.put(fieldName, pts);
                        }
                        else{
                            box.fields.put(fieldName, new HashSet<>(rightPointsTo));
                        }
                    }
                }

            }
        }
        else if (unit instanceof InvokeStmt) {
            InvokeStmt invokeStmt = (InvokeStmt) unit;
            InvokeExpr invokeExpr = invokeStmt.getInvokeExpr();
            if (invokeExpr instanceof StaticInvokeExpr) {
                StaticInvokeExpr staticInvokeExpr = (StaticInvokeExpr) invokeExpr;
                for (Value arg : staticInvokeExpr.getArgs()) {
                    markEscape(arg, newout);
                }
            }
            else if (invokeExpr instanceof VirtualInvokeExpr) {
                VirtualInvokeExpr virtualInvokeExpr = (VirtualInvokeExpr) invokeExpr;
                Value base = virtualInvokeExpr.getBase();
                if (base instanceof Local) {
                    markEscape(base, newout);
                }
                for (Value arg : virtualInvokeExpr.getArgs()) {
                    markEscape(arg, newout);
                }
            }
        } 
        else if (unit instanceof ReturnStmt) {
            ReturnStmt returnStmt = (ReturnStmt) unit;
            Value returnValue = returnStmt.getOp();
            if (returnValue != null) {
                markEscape(returnValue, newout);
            }
        }

        return newout;
    }

    private Box createBox(Unit unit, boolean dummy, SortedMap<Integer, Box> boxes){
        int line = unit.getJavaSourceStartLineNumber();
        if(dummy) line = - Math.abs(line);
        if(boxes.containsKey(line)) {
            return boxes.get(line);
        }
        else{
            Box box = new Box(line, dummy);
            boxes.put(line, box);
            return box;
        }
    }

    private boolean isLeftEscaping(Value leftOp, Map<String, Set<Box>> newout){
        if (leftOp instanceof Local) {
            Local leftLocal = (Local) leftOp;
            Set<Box> PointsTo = newout.getOrDefault(leftLocal.getName(), new HashSet<>());
            for(Box box : PointsTo){
                if(box.escape == true) return true;
            }
        }
        return false;
    }

    private void markEscape(Value value, Map<String, Set<Box>> newout){
        if (value instanceof Local) {
            Local valueLocal = (Local) value;
            Set<Box> PointsTo = newout.getOrDefault(valueLocal.getName(), new HashSet<>());
            escapeBoxSet(PointsTo);
        }
    }

    private void escapeBoxSet(Set<Box> boxset){
        for(Box box : boxset){
            if(box.escape == true) continue;
            box.escape = true;
            for (Map.Entry<String, Set<Box>> entry : box.fields.entrySet()) {
                Set<Box> fieldSet = entry.getValue();
                escapeBoxSet(fieldSet);
            }
        }
    }

    private void escapeBFS(Map<String, Set<Box>> newout){
        Set<Box> visited = new HashSet<>();
        Queue<Box> queue = new LinkedList<>();
        for (Set<Box> boxes : newout.values()) {
            queue.addAll(boxes);
        }
        while (!queue.isEmpty()) {
            Box currentBox = queue.poll();
            if (visited.contains(currentBox)) {
                continue;
            }
            visited.add(currentBox);
            if (currentBox.escape) {
                for (Set<Box> neighborBoxes : currentBox.fields.values()) {
                    queue.addAll(neighborBoxes);
                    for (Box neighborBox : neighborBoxes) {
                        neighborBox.escape = true;
                    }
                }
            }
        }
    }
}
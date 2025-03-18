import Language

/**
 * Key Material Concept
 * any class that implements `java.security.spec.KeySpec`
 */
class KeyMaterialObject extends Class {
  KeyMaterialObject() {
    exists(RefType t |
      this.extendsOrImplements*(t) and
      t.hasQualifiedName("java.security.spec", "KeySpec")
    )
  }
}

/**
 * KeyMaterial
 * ie some plain material that gets used to generate a Key
 */
class KeyMaterialInstantiation extends Crypto::KeyMaterialInstance instanceof ClassInstanceExpr {
  KeyMaterialInstantiation() {
    this.(ClassInstanceExpr).getConstructedType() instanceof KeyMaterialObject
  }

  override DataFlow::Node getOutputNode() { result.asExpr() = this }

  override DataFlow::Node getInputNode() {
    result.asExpr() = this.(ClassInstanceExpr).getArgument(0)
  }

  //TODO
  override predicate flowsTo(Crypto::FlowAwareElement other) { none() }
}

abstract class JCAKeyGenerationCall extends Call { }

private class JCAKeyGenerationCallWithMaterialArg extends JCAKeyGenerationCall {
  JCAKeyGenerationCallWithMaterialArg() {
    exists(string s | s in ["generatePrivate", "generatePublic", "translateKey"] |
      this.getCallee().hasQualifiedName("java.security", "KeyFactory", s)
    )
  }

  DataFlow::Node getInputData() { result.asExpr() = this.getArgument(0) }
}

private class JCAKeyGenerationCallWithoutMaterialArg extends JCAKeyGenerationCall {
  JCAKeyGenerationCallWithoutMaterialArg() {
    this.getCallee().hasQualifiedName("javax.crypto", "KeyGenerator", "generateKey")
  }

  DataFlow::Node getInputData() { result.asExpr() = this.getArgument(0) }
}

abstract class KeyGenerators extends Class {
  Method getInstance() { result = this.getAMethod() and result.hasName("getInstance") }

  abstract Method keySizeSetter();
}

class KeyGenerator extends KeyGenerators {
  KeyGenerator() { this.hasQualifiedName("javax.crypto", "KeyGenerator") }

  override Method keySizeSetter() { result = this.getAMethod() and result.hasName("init") }
}

class KeyFactory extends KeyGenerators {
  KeyFactory() { this.hasQualifiedName("java.security", "KeyFactory") }

  //todo this requires flow from a keyspec
  override Method keySizeSetter() { none() }
}

class KeyPairGenerator extends KeyGenerators {
  KeyPairGenerator() { this.hasQualifiedName("java.security", "KeyPairGenerator") }

  override Method keySizeSetter() { result = this.getAMethod() and result.hasName("initialize") }
}

/**
 * Data-flow configuration modelling flow from a string literal to a `KeyGeneratorsGetInstanceCall` argument.
 */
private module KeyGenAlgorithmStringToFetchFlow implements DataFlow::ConfigSig {
  //TODO narrow this type based on JCA standard names doc for whats possible here, like is done for the cipher algs
  predicate isSource(DataFlow::Node src) { src.asExpr() instanceof StringLiteral }

  predicate isSink(DataFlow::Node sink) {
    exists(KeyGenerators gen, Call c |
      c.getCallee() = gen.getInstance() and
      c.getArgument(0) = sink.asExpr()
    )
  }
}

module KeyGenAlgorithmStringToFetchFlowIns = DataFlow::Global<KeyGenAlgorithmStringToFetchFlow>;

/**
 * The key generation algorithm argument to a `KeyGeneratorsGetInstanceCall `.
 *
 * For example, in `KeyGenerator.getInstance(algorithm)`, this class represents `algorithm`.
 *
 * the algorithm is both what the resulting key is meant to be used for but also informs how it
 * was created
 */
class KeyDerivationAlgorithmArg extends Crypto::KeyDerivationAlgorithmInstance instanceof Expr {
  Call getInstanceCall;

  KeyDerivationAlgorithmArg() {
    exists(KeyGenerators gen |
      getInstanceCall.getCallee() = gen.getInstance() and this = getInstanceCall.getArgument(0)
    )
  }

  /**
   * Returns the `StringLiteral` from which this argument is derived, if known.
   */
  StringLiteral getOrigin() {
    KeyGenAlgorithmStringToFetchFlowIns::flow(DataFlow::exprNode(result),
      DataFlow::exprNode(this.(Expr).getAChildExpr*()))
  }

  Call getCall() { result = getInstanceCall }
}

/**
 * A data-flow configuration to track flow from a integer value to
 * the keysize argument of the various `init` methods of the KeyGeneratorsGetInstanceCall types
 */
private module IntToKeyGeneratorInitConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node src) { src.asExpr() instanceof IntegerLiteral }

  predicate isSink(DataFlow::Node sink) {
    exists(KeyGenerators c, Call call |
      call.getCallee() = c.keySizeSetter() and call.getArgument(0) = sink.asExpr()
    )
  }
}

module IntToKeyGeneratorInitConfigFlow = DataFlow::Global<IntToKeyGeneratorInitConfig>;

/**
 * Data-flow configuration modelling flow from a keygenerator type getinstance call
 * to generation step
 */
module KeyDerivationOperationInstanceConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node src) {
    exists(Call getInstanceCall, KeyGenerators kg |
      kg.getInstance() = getInstanceCall.getCallee() and
      src.asExpr() = getInstanceCall
    )
  }

  predicate isSink(DataFlow::Node sink) {
    exists(JCAKeyGenerationCall call | sink.asExpr() = call.getQualifier())
  }

  predicate isAdditionalFlowStep(DataFlow::Node node1, DataFlow::Node node2) {
    exists(Call getInstanceCall, KeyGenerators kg, Call keySizeSetterCall |
      kg.getInstance() = getInstanceCall.getCallee() and
      node1.asExpr() = getInstanceCall.getQualifier() and
      kg.keySizeSetter() = keySizeSetterCall.getCallee() and
      node2.asExpr() = keySizeSetterCall.getQualifier()
    )
  }
}

module KeyDerivationOperationInstanceConfigFlow =
  DataFlow::Global<KeyDerivationOperationInstanceConfig>;

class KeyDerivationOperationInstance extends Crypto::KeyDerivationOperationInstance instanceof Call {
  Crypto::KeyDerivationAlgorithmInstance algorithm;
  JCAKeyGenerationCall generateCall;

  KeyDerivationOperationInstance() {
    exists(KeyDerivationAlgorithmArg arg, DataFlow::Node source, DataFlow::Node sink |
      this = generateCall and
      generateCall.getQualifier() = sink.asExpr() and
      KeyDerivationOperationInstanceConfigFlow::flow(source, sink) and
      algorithm = arg and
      source.asExpr() = arg.getCall()
    )
  }

  //TODO fill these out using various flows defined above
  override Crypto::KeyDerivationAlgorithmInstance getAlgorithm() { result = algorithm }

  override Crypto::KeyMaterialInstance getInputKeyMaterial() { none() }

  override Crypto::KeyArtifactInstance getOutputKey() { none() }
    //exists(KeyObject key | result = key and key.getOutputNode() = this) }
}

/**
 * A Key Object
 */
class KeyObject extends Crypto::KeyArtifactInstance instanceof Variable {
  Crypto::KeyDerivationOperationInstance instantiation;

  KeyObject() {
    exists(RefType t |
      instantiation = this.getInitializer() and
      this.getType().(RefType).extendsOrImplements*(t) and
      t.hasQualifiedName("java.security", "Key")
    )
  }

  override DataFlow::Node getOutputNode() { result.asExpr() = instantiation }

  //TODO fix by using the KeyDerivationOperationInstance type in this type
  override DataFlow::Node getInputNode() {
    result.asExpr() = instantiation
  }

  override DataFlow::Node getKeySize() { exists(DataFlow::Node src, DataFlow::Node sink, Call initcall
  | 
  IntToKeyGeneratorInitConfigFlow::flow(src, sink)
  and result = src
  and initcall.getArgument(0) = sink.asExpr()
  //init qualifier same as keygen qualifier, we need to use more of the connected concepts tho, this is re-inventing them every time we need something
and initcall.getQualifier() = instantiation.(JCAKeyGenerationCall).getQualifier().(VarAccess).getVariable().getAnAccess()

)
}

  //TODO
  override predicate flowsTo(Crypto::FlowAwareElement other) { none() }
}

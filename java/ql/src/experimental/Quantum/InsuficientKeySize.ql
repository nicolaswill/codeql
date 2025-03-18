/**
 * @name Use of a cryptographic algorithm with insufficient key size
 * @description Using cryptographic algorithms with too small a key size can
 *              allow an attacker to compromise security.
 * @kind path-problem
 * @problem.severity warning
 * @security-severity 7.5
 * @precision high
 * @id java/insufficient-key-size-new-model
 * @tags security
 *       external/cwe/cwe-326
 */

//this query is a replica of the concept in: https://github.com/github/codeql/blob/main/java/ql/src/Security/CWE/CWE-326/InsufficientKeySize.ql
//but uses the **NEW MODELLING**
//AND is actually only a subset of the logic -
//precisely this currently detects insuffficient key size for AES
import experimental.Quantum.Language

/** Returns the minimum recommended key size for AES. */
int minSecureKeySizeAes() { result = 128 }

//todo make this actually check to match the alg to AES (some JCA model improve required)
//currently looks for any key size lower than...
from Crypto::KeyArtifactInstance key
where key.getKeySize().asExpr().(IntegerLiteral).getIntValue() < minSecureKeySizeAes()
select key, "This $@ is less than the recommended key size of " + minSecureKeySizeAes() + " bits.",
  key.getKeySize(), "key size"

package com.diffblue.java_testcase;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Modifier;
import java.util.Arrays;
import java.util.Optional;

import javassist.CannotCompileException;
import javassist.ClassPool;
import javassist.CtBehavior;
import javassist.CtClass;
import javassist.CtMethod;
import javassist.CtConstructor;
import javassist.NotFoundException;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.SignatureAttribute;
import javassist.bytecode.SignatureAttribute.MethodSignature;

import org.objenesis.ObjenesisStd;

/**
 * Describe class <code>Reflector</code> here.
 *
 * @author Matthias Guedemann
 * @version 1.0
 */
public final class Reflector
{
  private Reflector() {}

  private static <T> void setInstanceField(Class<T> c, Object o, String fieldName, Object newVal)
    throws NoSuchFieldException, IllegalArgumentException, IllegalAccessException
  {
    if (c == null) throw new NoSuchFieldException();
    Optional<Field> field = Arrays.stream(c.getDeclaredFields()).filter(f -> f.getName().equals(fieldName)).findAny();
    if (!field.isPresent()) setInstanceField(c.getSuperclass(), o, fieldName, newVal);
    else
    {
      Field property = field.get();
      property.setAccessible(true);

      // remove final modifier
      Field modifiersField = Field.class.getDeclaredField("modifiers");
      modifiersField.setAccessible(true);
      modifiersField.setInt(property, property.getModifiers() & ~Modifier.FINAL);

      try {
        property.set(o, newVal);
      } catch (IllegalAccessException e) {
        throw new RuntimeException(e); // Should never happen.
      }
    }
  }

  /**
   * Changes a given field of an object instance via reflection, bypassing the
   * private modifier.
   *
   * @param o an <code>Object</code> instance to change
   * @param fieldName a <code>String</code> the name of the field to change
   * @param newVal an <code>Object</code> the new value for the field
   *
   * @throws NoSuchFieldException if a field with the specified name is not found.
   * @throws IllegalArgumentException if the specified object is not an instance of the class or interface declaring the underlying field (or a subclass or implementor thereof), or if an unwrapping conversion fails.
   */
  public static void setInstanceField(Object o, String fieldName, Object newVal) throws NoSuchFieldException, IllegalArgumentException, IllegalAccessException
  {
    setInstanceField(o.getClass(), o, fieldName, newVal);
  }

  public static String removePackageFromName(String className)
  {
    int lastSeparator = className.lastIndexOf('.');
    if(lastSeparator != -1)
      return className.substring(lastSeparator + 1);
    else
      return className;
  }

  /**
   * This forces the creation of an instance for a given class name.
   *
   * @param className a <code>String</code> giving the name of the class
   * @return an <code>Object</code> which is an instance of the specified class
   * @throws ClassNotFoundException if the class cannot be found in the
   * classpath
   */
  public static Object forceInstance(String className)
    throws ClassNotFoundException, NotFoundException,
    CannotCompileException, InstantiationException, IllegalAccessException,
    BadBytecode
  {
    ClassPool pool = ClassPool.getDefault();
    CtClass c = pool.get(className);

    // we consider a class abstract if any method has no body
    if(isAbstract(c) || c.isInterface())
    {
      String packageName = "com.diffblue.test_gen.";
      String newClassName = packageName + removePackageFromName(className);

      CtClass implementation = pool.makeClass(newClassName + "_implementation");

      if(c.isInterface())
        implementation.setInterfaces(new CtClass[]{ c });
      else
        implementation.setSuperclass(c);

      // look for constructor
      // create default constructor if none exists
      if(c.isInterface())
      {
        CtConstructor ctor = new CtConstructor(new CtClass[]{ }, implementation);
        ctor.setBody("{}");
        implementation.addConstructor(ctor);
      }

      // declared methods or only methods ?
      for(CtMethod m : c.getDeclaredMethods())
      {
        if(m.isEmpty())
        {
          String methodBody = getDefaultBody(m.getReturnType());
          String prefix = "param_";
          int number = 0;
          boolean first = true;
          String parameter = "";
          for(CtClass param : m.getParameterTypes())
          {
            if(!first)
              parameter +=", ";
            else
              first = false;
            parameter += param.getName() + " " + prefix + number;
            number++;
          }

          String methodSignature = "public " + m.getReturnType().getName() + " "
            + m.getName() + "(" + parameter + ")";
          CtMethod.make(methodSignature + methodBody, implementation);
        }
      }
      int modifiers = implementation.getModifiers();

      return forceInstance(implementation.toClass());
    }
    else
      return forceInstance(Class.forName(className));
  }

  private static boolean isAbstract(CtClass c)
  {
    for(CtMethod m : c.getDeclaredMethods())
      if(m.isEmpty())
        return true;
    return false;
  }

  private static String getDefaultBody(CtClass returnType)
    throws CannotCompileException, NotFoundException
  {
    if(returnType == CtClass.booleanType)
      return "{ boolean b; return b;}";
    else if (returnType == CtClass.byteType)
      return "{ byte b; return b;}";
    else if (returnType == CtClass.charType)
      return "{ char c; return c;}";
    else if (returnType == CtClass.doubleType)
      return "{ double d; return d;}";
    else if (returnType == CtClass.floatType)
      return "{ float f; return f;}";
    else if (returnType == CtClass.intType)
      return "{ int i; return i;}";
    else if (returnType == CtClass.longType)
      return "{ long l; return l;}";
    else if (returnType == CtClass.shortType)
      return "{ short s; return s;}";
      // do nothing
    else if (returnType == CtClass.voidType)
      return "{ return; }";
      // return null for all non-atomic types
    else
      return "{ return null; }";
  }

  private static Optional<Constructor<?>> getDefaultConstructor(Class<?> c)
  {
    return Arrays.stream(c.getDeclaredConstructors()).filter(ctor -> ctor.getParameterCount() == 0).findAny();
  }

  /**
   * This forces the creation of an instance for a given class name. If the
   * class provides a public default constructor, it is called. If the class has
   * a private default constructor, it is made accessible and then called.
   *
   * @param c a <code>Class</code> the class to instantiate
   * @return an <code>Object</code> which is an instance of the specified class
   */
  @SuppressWarnings("unchecked")
  public static <T> T forceInstance(Class<T> c)
  {

    Optional<Constructor<?>> ctor = getDefaultConstructor(c);
    if (ctor.isPresent())
    {
      Constructor<?> defaultCtor = ctor.get();
      defaultCtor.setAccessible(true);
      try { return (T) defaultCtor.newInstance(); }
      catch (InstantiationException | InvocationTargetException | IllegalAccessException e) {}
    }
    return new ObjenesisStd().newInstance(c);
  }
}

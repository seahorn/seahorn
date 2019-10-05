#include "llvm/Support/raw_ostream.h"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/SymStore.hh"

namespace seahorn
{
  /// true if v is a constant value
  static bool isValue (Expr v)
  {
    return isOpX<TRUE> (v) || isOpX<FALSE> (v) || 
      isOpX<MPZ> (v) || isOpX<MPQ> (v);
  }
  
  
  void SymStore::swap (SymStore &o)
  {
    assert (&m_efac == &o.m_efac);
      
    std::swap (m_Parent, o.m_Parent);
    std::swap (m_ownedParent, o.m_ownedParent);
    std::swap (m_Store, o.m_Store);
    std::swap (m_trackUse, o.m_trackUse);
    std::swap (m_uses, o.m_uses);
    std::swap (m_defs, o.m_defs);
    std::swap (m_defs_sz, o.m_defs_sz);
  }  
  
  void SymStore::print (llvm::raw_ostream &out)
  {
    out << "SYMSTORE BEGIN\n";
    for (auto p : m_Store)
      out << *p.first << ": " << *p.second << "\n";
    out << "SYMSTORE END\n";
  }
  
  /// write val to key
  void SymStore::write (Expr key, Expr val) 
  { 
    assert (!isValue (key));
    
    m_Store[key] = val; 
    if (m_trackUse) m_defs.push_back (key);
  }
    
  /// assign non-deterministic value to key. Returns the new value.
  Expr SymStore::havoc (Expr key)
  {
    // assert (!isValue (key));
    if (isValue (key)) return key;
    
    Expr val;
      
    if (m_Parent) val = m_Parent->havoc (key);
    else 
    {
      val = at (key);
      
      Expr fdecl = val ? bind::fname (val) : bind::fname (key);
        
      Expr fname = bind::fname (fdecl);
      int idx = 0;
      if (val)
      {
        idx = variant::variantNum (fname) + 1;
        fname = variant::mainVariant (fname);
      }
      
      fname = variant::variant (idx, fname);
      val = bind::reapp (val ? val : key, bind::rename (fdecl, fname));
    }
      
    write (key, val);
    return val;
  }
    
  /// Read key from the store. Creates new value if needed
  Expr SymStore::read (Expr key)
  {
    if (isValue (key)) return key;
    
    Expr val = at (key);
    if (val) return val;
      
    if (m_Parent) val = m_Parent->havoc (key);
    else 
    {
      Expr fdecl = bind::fname (key);
      Expr fname = bind::fname (fdecl);
      fname = variant::variant (0, fname);
      val = bind::reapp (key, bind::rename (fdecl, fname));
    }      
      
    if (m_trackUse) m_uses.push_back (key);
      
    LOG("live", 
        llvm::errs () << "Store reading: " << *key << " uses " << m_uses.size () << "\n");
      
    {
      detail::scoped_track_use stu (*this, false);
      write (key, val);
    }
      
    return val;
  }
  
  
  const ExprVector &SymStore::defs () 
  {
    if (m_defs.size () > m_defs_sz)
    {
      std::sort (m_defs.begin (), m_defs.end ());
      auto last = std::unique (m_defs.begin (), m_defs.end ());
      m_defs.resize (std::distance (m_defs.begin (), last));
      m_defs_sz = m_defs.size ();
    }
      
    return m_defs;
  }

  
  namespace detail
  {
    VisitAction seahorn::detail::SymStoreEvalVisitor::operator() (Expr exp) const
    {
      if (m_store.isDefined (exp))
        return VisitAction::changeTo (m_store.at (exp));
      
      else if (expr::op::bind::isFdecl (exp) || isOpX<BIND> (exp))
        return VisitAction::skipKids ();
      
      return VisitAction::doKids ();
    }
    
    scoped_track_use::scoped_track_use (SymStore &s, bool trackUse) :
      m_s (s), m_trackUse (s.m_trackUse) { s.m_trackUse = trackUse; }
    scoped_track_use::~scoped_track_use () { m_s.m_trackUse = m_trackUse; }
  }

}



## pp is a squarefree polynomial in v,
## that is, pp is in Q[v]
## qq is a polynomial in y modulo pp, that is, qq 
## qq is in Q[z,v] / <pp(z)>
## R is the polynomial ring over Q[v,z]

Trager_base := proc(pp, v, qq, z, R, printing?:=false) 
local final, r, s, d, gcD, q, p, u, h_temp, f, temp_fac, i, Tasks, Results, task, f_task, p_task, i_task, h_task, rc, out, k, j, res, resmod, px, newtask, midElement;
local qq_temp;
    final := []; 
    r := resultant(pp, qq, v); 
    
    s := 0; d := diff(r, z); 
    gcD := gcd(r, d); 
    q := qq; p := pp; 

    if printing? then
        print("r", r); 
        print("d", d); 
        print("r", r);
    end if;
    
    while degree(gcd(r, d), z) <> 0 
    do s := s + 1; 
        q := eval(qq, z = z - s*v);
        if printing? then print("q", q); end if;
        q := rem(q, p, v, 'q1'); 
        r := resultant(p, q, v); 
        if printing? then print("q===", q);  
        print("r", r); end if;
        d := diff(r, z); 
        if printing? then print("gcd_rd", gcd(r, d)); end if;
    end do;
    
    if printing? then print("final _s", s); end if;
    f := factors(r); 
    if printing? then print("f:=", f);  end if;
    temp_fac := [];
    
    for i to nops(f[2]) do 
        temp_fac := [op(temp_fac), f[2][i][1]];
    end do; 
    
    rc := Chain([p], Empty(R), R); 
    Tasks := [[q, temp_fac, 1, rc]]; 
    
    Results := []; 
    if printing? then print("Tasks", Tasks[1]);  end if;
    if nops(f[2]) = 1 then 
        Results := [op(Results), [qq, [qq], 1, rc]]; 
    end if;
    
    while 0 < nops(Tasks) 
    do  task := Tasks[1]; 
        Tasks := {op(Tasks[2 .. nops(Tasks)])};
        if printing? then print("Tasks=", Tasks); end if;
        f_task := task[1]; h_task := task[2]; i_task := task[3];
        if printing? then print("i_task=", i_task); end if;
        p_task := Polynomial(v, task[4], R); 
        if printing? then print("t=", nops(f[2]));end if;
        
        if nops(f[2]) < i_task then 
            h_temp := []; 
            for u to nops(h_task) do 
                if type(h_task[u], 'constant') = 'false' 
                then h_temp := [op(h_temp), h_task[u]/lcoeff(h_task[u])]; 
                end if; 
            end do; 
            h_task := h_temp; 
            Results := [op(Results), [qq, h_task, 1, task[4]]];
            if printing? then  print("results", Results); end if;
        else     
            rc := task[4]; 
            out := RegularGcd(h_task[i_task], f_task, z, rc, R);
            k := nops(out); 
            if printing? then print("k", k); print("out", out); end if;
            for j to k do 
                px := Polynomial(v, out[j][2], R); 
                res := out[j][1]; 
                resmod := eval(res, z = z + s*v); 
                resmod := rem(resmod, px, v, 'q1'); 
                midElement := [op(h_task[1 .. i_task - 1]), resmod, op(h_task[i_task + 1 .. ()])];
                newtask := [q, midElement, i_task + 1, out[j][2]]; 
                if printing? then print("neewtask=", newtask); end if;
                Tasks := [op(Tasks), newtask]; 
            
                if printing? then print("Tasks=", Tasks); end if;
            end do;
        end if;
    end do; 
    return Results; 
end proc;
############################################################Extennded Trager######################################################
##############################################################################################################################
##################################################################################################################################


ExtendedTrager:=proc(qq,T,n,printing?:=False)
    local l := 0,  X := [seq(x[i], i = 1 .. n)],
    temp_fac, task, f_task, p_task, i_task, h_task, midElement, res, resmod, rc_task, s_task, ans ,t :=0, step1 := [], 
    javab := [], s := 0, d := 1,
    R := PolynomialRing([z, seq(X[n - i + 1], i = 1 .. n)]), rc := Chain(T, Empty(R), R), 
    
    r := 0, j := 0, k := 0, newtask := 0, r_task := 0, d_task := 0, gcd_task := 0,
    
    
    chain_new := rc,  
    q := qq,  base:=qq, Tasks := [[q, gcd_task, s, rc]], Results := [],  out := rc, D, qq_temp;
    
                                                                                if printing? then  print(" level of  the regular chain  ===",n); end if;
                                                                                if printing? then  print("X==",X);   end if;
     n_temp := n;
     n_n:=n_temp;
   
     print("n=",n);
     #n:=n_n
     
     if n = 1 then
                                                                                if  printing? then print("level of  process :=======================>=", n); end if;
          R:= PolynomialRing([z, x[1]]);
          ans := Trager_base(T[1], x[1], qq, z, R);
          
                                                                               if  printing? then print("ans====", ans); end if; 
                                                                                # if  printing? then print("Equations====", Equations(ans[1][4],R)); end if;    
               
          return ans;
      
    end if;
    R := PolynomialRing([z, seq(X[n - i + 1], i = 1 .. n)]);              if  printing? then print( "R-polyring:=",R);   end if;  
    rc := Chain(T, Empty(R), R);                                                                 if  printing? then print("Tasks=", Tasks); end if;
    while nops(Tasks)>0  do ;
    
      task := Tasks[1];
                                                                              if printing? then  print("task=", task); end if;
      Tasks := {op(Tasks[2 .. nops(Tasks)])};
                                             
                                                                                 if  printing? then print("Tasks=", Tasks); end if;
                                                                                 if  printing? then print("task[1]",task[1]); end if; 
      q := task[1];
      gcd_task := task[2];
      s := task[3];
      chain_new := task[4];
      
      
     
      
      if degree(gcd_task, z) = 0 then:                                             # make  square  free
      
        
          
         Results:=[ op(Results),task];                                         if  printing?  then print("results",  Results);  end if; 
                                                                               if  printing?  then print("Results inside###",  Results);  end if;  
         
         else:      
                                                                               if  printing? then print( "qq:=",qq); end if; 
         s := s + 1;   
         q := eval(qq, z = z - s*X[n]);                                         if  printing? then print( "R:=",R);   end if;  
                                                                               if  printing? then print( "q:=, s=",q, s);   end if; 
             
         
         
         qq_temp:= NormalForm(q, rc, R);                                       if  printing? then print( "q_temp=",qq_temp);   end if;   
         r := resultant(qq_temp, T[n], x[n]);
                                                                               if  printing? then print("r:=",r);   end if;  
         d := diff(r, z);   
                                                                               if  printing? then  print("d:=",d);   end if;  
                                                                          
         out := RegularGcd(r, d, z, rc, R);     
                                                                               if  printing? then  print("rc:=", Equations(rc,R));   end if; 

         
          
                                                                               if     printing?  then print("out=",out); end if; 
                                                                               if  printing? then  print("out[1][2]:=", Equations(out[1][2],R));   end if; 
         k := nops(out);                                                       if  printing? then  print("out size k:=", k);   end if; 
         
         for j from 1 to k do
            chain_new := out[j][2];
            gcd_task := out[j][1];
            newtask := [qq_temp, gcd_task, s, chain_new];
            Tasks := [op(Tasks), newtask];
                                                                 
                                                                           
                                                                                   if  printing? then  print("new task in out=====", newtask);   end if; 
                                                                                   if  printing? then  print("Tasks_in side=", Tasks);   end if; 
                                                                                   if  printing? then  print("nops(task)infor", nops(Tasks));   end if; 
        end do;      
         end if;
         
    
    end do;
      
   ################################################   end While   
   local  qq_rec;
   step1 := Results;
                                                                                     if  printing? then  print("step1", step1);   end if;  
   Results := [];
                                                                                     if  printing? then  print("Results", Results);   end if; 
    R := PolynomialRing([z, seq(X[n - i + 1], i = 1 .. n)]);
   
   for t  from 1 to nops(step1) do
   
         qq_rec := step1[t][1];                                                     if printing? then print("qq_rec=",qq_rec); end if;
         s_rec := step1[t][3];
         old_chain:=step1[t][4];
         oldRC_num:=nops(Equations(old_chain,R));
                                                                                    if printing? then  print("oldRC_num:====##>",Equations(old_chain,R)) ; end if;
                                                                                    if  printing? then  print("[seq(old_chain[i], i = 1 .. oldRC_num - 1)]:=",[seq(Equations(old_chain,R)[i], i = oldRC_num .. 2)]); end if;
                                                                                    
         
         r := resultant(qq_rec, T[n], x[n]);                                        if printing? then  print("r",r); end if;
         #ans := ExtendedTrager(r, [seq(T[i], i = 1 .. n - 1)], n - 1,true);             
         ans := ExtendedTrager(r, [seq(Equations(old_chain,R)[i], i = oldRC_num .. 2)], n - 1,true);
         
         
         
                                                                                      if  printing? then  print("ans@@@for loop    @@@@@==",ans[1]);   end if;      # [q,fctors,1,rc]
         
         for l from 1 to  nops(ans)  do;
                 Tasks:=[ans[l]];        # needed   a  new list                            if  printing? then  print("mean level:=",ans[l]);   end if;
                 
                 while(nops(Tasks)>0)     do;
                     
                
                     task:=Tasks[1];                                                         if  printing? then  print("Task[1]=--->",task);  end if; 
                     Tasks:={op(Tasks[2..nops(Tasks)])};
                    
                     print("Tasks=",Tasks);
                     
                     f_task:= qq_rec;
                     s_task:=s_rec;                                                           #coming from results
                     h_task:= task[2];
                     i_task:= task[3];
                                                                                              if  printing? then print("h_task_=",h_task);  end if;  
                    
                     rc_task := task[4];  
                
                                                                                           if  printing? then print("rc_task=",rc_task);  end if;       
                     if i_task =1 then;                                                  # just once
                                                                                           if  printing? then print("eq=",Equations(rc_task, R));  end if; 
                        
                       
                        R := PolynomialRing([z, seq(X[n - i + 1], i = 1 .. n)]);
                     
                                                                                           if  printing? then print("! (Equations(old_chain, R))==", Equations(old_chain, R));  end if; 
                                                                                            if  printing? then print(" !S(Equations(rc_task, R))==", Equations(rc_task, R));  end if; 
                                                                      
                     #list_rc := RegularizeInitial(Equations(old_chain, R)[1], rc_task, R); 
                       
                        
                      
                                                                 
                    ######################################add the cahin
                      rc_task := Chain([Equations(old_chain,R)[1]], rc_task, R);
                        
                                                                                               if  printing? then print("rc_task=>>>>>>>",Equations(rc_task,R));  end if;                                         
                                            
                        
                        
                      
                     end if;
                     
                     if nops(h_task) < i_task then;
                     
                                                                                                      if  printing? then print("#########################");  end if;  
                        Results := [op(Results), [qq, h_task, 1, rc_task]];
                                                                                                     if  printing? then print("results", Results);  end if;  
                     else;
                                                                                            if  printing? then print("h_task[i_task]=, f_task=,rc_task=",h_task[i_task],f_task,Equations(rc_task,R)); end if; 
                     
                         out:= RegularGcd(h_task[i_task], f_task, z, rc_task, R);                    if  printing? then print("out_regulargcd",out); end if;  
                                                                                                      if  printing? then print("regular  chain=");   print(Equations(out[1][2], R)); end if; 
                         k := nops(out);
                         
                        
                         for j  from 1 to k do;
                            
                             
                             chain_new := out[j][2];
                             
                             res := out[j][1];                                                        if  printing? then print("out[j][1]=  ",out[j][1]); end if; 
                             resmod := eval(res, z = s_task*X[n] + z);                              
                             resmod := NormalForm(resmod, out[j][2], R);                             if  printing? then print("resmod==",resmod); end if;  
                             
                             
                             midElement := [op(h_task[1 .. i_task - 1]), resmod/lcoeff(resmod), op(h_task[i_task + 1 .. ])];
                             newtask := [f_task, midElement, i_task + 1, out[j][2]];
                                                                                                            if  printing? then print("neewtask=", newtask); end if; 
                                           
                             Tasks := [op(Tasks), newtask];                                                 if  printing? then print("Tasks=", Tasks); end if;  
                             
                          end do;
                             
                        
                     
                     end if;
    
                
            
          end  do;
    
     
   
   
      end do;
   end do;
   ####################################################################verification
   RR := PolynomialRing([z, seq(X[n - i + 1], i = 1 .. n)]);
   rc_temp := Chain(T, Empty(RR), RR);
   
   for i  from 1 to nops(Results) do;
      prod:=expand( simplify(product(Results[i][2][b], b = 1 .. nops(Results[i][2])))) ;
                                                                                 
      prodmod := NormalForm(prod-0, rc_temp, RR);                                    print("prodmmod=",prodmod); 
      
      
          if prodmod=0 then;
              valid:=1;
          else;
               valid:=0; 
          end if;
    end do;
   
   if valid=1 then:
      print("verified!!!");
      
   else;
      print("not verified!!!");
   end if;
   #################################################################################
                                                                               
   return Results;
   
    
    
end proc;
#lcoeff

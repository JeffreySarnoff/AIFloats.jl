

kmin = 14
kmax = 14

ufs = [AIFloat(k, p, :unsigned, :finite)    for k in kmin:kmax for p in  1:k];
ues = [AIFloat(k, p, :unsigned, :extended)  for k in kmin:kmax for p in  1:k];
sfs = [AIFloat(k, p, :signed, :finite)      for k in kmin:kmax for p in  1:k-1];
ses = [AIFloat(k, p, :signed, :extended)    for k in kmin:kmax for p in  1:k-1];

uftypes = map(typeof, ufs);
uetypes = map(typeof, ues);
sftypes = map(typeof, sfs);
setypes = map(typeof, ses);

ufabstypes = map(supertype, uftypes);
ueabstypes = map(supertype, uetypes);
sfabstypes = map(supertype, sftypes);
seabstypes = map(supertype, setypes);

ufvals = map(floats, ufs);
uevals = map(floats, ues);
sfvals = map(floats, sfs);
sevals = map(floats, ses);

frexp_ufvals = map(clean_frexp, ufvals);
frexp_uevals = map(clean_frexp, uevals);
frexp_sfvals = map(clean_frexp, sfvals);
frexp_sevals = map(clean_frexp, sevals);

clean_ufvals = map(ldexp, frexp_ufvals);
clean_uevals = map(ldexp, frexp_uevals);
clean_sfvals = map(ldexp, frexp_sfvals);
clean_sevals = map(ldexp, frexp_sevals);

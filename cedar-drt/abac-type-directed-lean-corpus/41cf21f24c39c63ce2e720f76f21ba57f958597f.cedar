@r("")
@r3sssss("6666666\0\0\0\0\0\0\06")
permit(
  principal == A0::"",
  action,
  resource == t::"\t"
) when {
  (true && ((decimal(action["r3sssss"])).greaterThanOrEqual(decimal(principal["r3sssss"])))) && ((ip(principal["r3sssss"])).isIpv4())
};

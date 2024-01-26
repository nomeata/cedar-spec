forbid(
  principal == a::"",
  action,
  resource == a::""
) when {
  ((true && ([[]].containsAll(if ((ip("54.54.54.62")).isIpv4()) then [[], []] else [[]]))) && ((principal["Bsss"]).contains(55497851173798659))) && (a::"\0" has "Bsss")
};

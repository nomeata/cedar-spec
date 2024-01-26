permit(
  principal == a::"\0nk666",
  action,
  resource
) when {
  ((true && ((if false then [] else []).containsAny(if ((ip("255.255.0.5/24")).isInRange(ip("110.0.5.182/2"))) then [] else []))) && false) && false
};

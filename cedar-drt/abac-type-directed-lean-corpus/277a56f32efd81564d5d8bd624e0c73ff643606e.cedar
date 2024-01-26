forbid(
  principal,
  action,
  resource is a in a::"\0\06"
) when {
  (true && (a::"\0\06" is a)) && (if false then (action is a) else true)
};

forbid(
  principal,
  action,
  resource in a::"\0\06"
) when {
  (true && (a::"\0\06" is a)) && (if false then false else (action is a))
};

import collections
from itertools import ifilterfalse

#a function factory seems to be faster than a class instance
def LruCache(user_function, maxsize=100, keymap=None, shared_parameters=None):
    """
    user_function is the function that generates the cache-able objects and that should be
    wrapped by this factory.

    Arguments to the cached function must be hashable.
    Cache performance statistics stored in f.hits and f.misses.
    Clear the cache with f.clear().
    http://en.wikipedia.org/wiki/Cache_algorithms#Least_Recently_Used

    keymap is a function that builds custom keys from actual args.
    """

    maxqueue = maxsize * 10
    
    if shared_parameters == None:
        cache = {}                       # mapping of args to results
        queue = collections.deque()      # order that keys have been used
        refcount = collections.Counter() # times each key is in the queue
    else:
        cache, queue, refcount = shared_parameters

    sentinel = object()              # marker for looping around the queue
    kwd_mark = object()              # separate positional and keyword args
    fun_mark = object()              # separate user_function from arguments

    # lookup optimizations (ugly but fast)
    queue_append, queue_popleft = queue.append, queue.popleft
    queue_appendleft, queue_pop = queue.appendleft, queue.pop

    def wrapper(*args, **kwds):
        # cache key records both positional and keyword args
        if keymap == None:
            key = args
            if shared_parameters != None:
                # if we share the cache between different functions we need to tag them
                # the original cache would be the untagged one. 
                key += (fun_mark, user_function)
            if kwds:
                key += (kwd_mark,) + tuple(sorted(kwds.items()))
        else:
            key = keymap(args, kwds, kwd_mark, fun_mark, user_function)

        # get cache entry or compute if not found
        try:
            result = cache[key]
            wrapper.hits += 1

            # record recent use of this key
            queue_append(key)
            refcount[key] += 1
        except KeyError:
            try:
                result = user_function(*args, **kwds)
            except:
                raise
            else:
                # record recent use of this key
                queue_append(key)
                refcount[key] += 1
                
            cache[key] = result
            wrapper.misses += 1

            # purge least recently used cache entry
            if len(cache) > maxsize:
                key = queue_popleft()
                refcount[key] -= 1
                while refcount[key]:
                    key = queue_popleft()
                    refcount[key] -= 1
                del cache[key], refcount[key]

        # periodically compact the queue by eliminating duplicate keys
        # while preserving order of most recent access
        if len(queue) > maxqueue:
            refcount.clear()
            queue_appendleft(sentinel)
            for key in ifilterfalse(refcount.__contains__,
                                    iter(queue_pop, sentinel)):
                queue_appendleft(key)
                refcount[key] = 1


        return result

    def clear():
        cache.clear()
        queue.clear()
        refcount.clear()
        wrapper.hits = wrapper.misses = 0

    wrapper.hits = wrapper.misses = 0
    wrapper.clear = clear
    wrapper.shared_parameters = (cache, queue, refcount)
    
    return wrapper
